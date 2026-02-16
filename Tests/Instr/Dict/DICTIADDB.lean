import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIADDB

/-
INSTRUCTION: DICTIADDB

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch branch
   - `.dictSetB true false .add` is handled by `execInstrDictDictSetB`.
   - Any non-`dictSetB` instruction must pass through to `next`.

2. [B2] Runtime success path: missing key (add-miss)
   - `VM.popNatUpTo 1023` and argument checks pass.
   - `dictSetBuilderWithCells` inserts the key and returns `ok = true`.
   - Runtime pushes updated dictionary cell then `-1`.

3. [B3] Runtime success path: existing key (add-hit)
   - Existing key returns `ok = false`.
   - Runtime pushes original dictionary root then `0`.

4. [B4] Runtime argument order and underflow
   - Global `VM.checkUnderflow 4` runs before any pops.
   - If there are fewer than four values, `.stkUnd` is raised.

5. [B5] Runtime argument validation
   - `n` must be integer and in `[0, 1023]`.
   - dict must be `.null` or `.cell`.
   - key must be integer, in range for signed width.
   - value must be builder.

6. [B6] Runtime dictionary validation branch
   - A malformed existing root can throw `.dictErr`.

7. [B7] Assembler behavior
   - `.dictSetB true false .add` and `.dictSetB true true .add` are supported by the assembler.
   - Assembly should round-trip via decoder.

8. [B8] Decoder behavior
   - `0xf452` decodes to `.dictSetB true false .add`.
   - `0xf451` / `0xf453` decode to ADDB/UADDB variants.
   - `0xf450` and `0xf454` decode as `.invOpcode`.

9. [B9] Gas accounting
   - `computeExactGasBudget` should succeed on add-hit branch (`created = 0`).
   - `computeExactGasBudgetMinusOne` should fail with insufficient gas.

TOTAL BRANCHES: 9
-/

private def dictIAddBId : InstrId := { name := "DICTIADDB" }
private def dictIAddBInstr : Instr := .dictSetB true false .add

private def dictIAddBCode : Cell := Cell.mkOrdinary (natToBits 0xf452 16) #[]
private def dictIAddBCodeADDB : Cell := Cell.mkOrdinary (natToBits 0xf451 16) #[]
private def dictIAddBCodeUADDB : Cell := Cell.mkOrdinary (natToBits 0xf453 16) #[]
private def dictADDBLowerInvalid : Cell := Cell.mkOrdinary (natToBits 0xf450 16) #[]
private def dictADDBUpperInvalid : Cell := Cell.mkOrdinary (natToBits 0xf454 16) #[]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b01010 5) #[]

private def builderVal : Builder :=
  Builder.empty.storeBits (natToBits 1 1)

private def signedRangeMax (n : Nat) : Int :=
  if n = 0 then 0 else (intPow2 (n - 1)) - 1

private def signedRangeMin (n : Nat) : Int :=
  if n = 0 then 0 else -(intPow2 (n - 1))

private def mkDictCellSigned (n : Nat) (k : Int) : Cell :=
  match dictKeyBits? k n false with
  | none => panic! "mkDictCellSigned: invalid signed key"
  | some keyBits =>
      match dictSetBuilderWithCells none keyBits builderVal .set with
      | .ok (some root, _, _, _) => root
      | _ => panic! "mkDictCellSigned: failed to build dict"

private def mkAddDictCellSigned (n : Nat) (k : Int) : Cell :=
  match dictKeyBits? k n false with
  | none => panic! "mkAddDictCellSigned: invalid signed key"
  | some keyBits =>
      match dictSetBuilderWithCells none keyBits builderVal .add with
      | .ok (some root, _, _, _) => root
      | _ => panic! "mkAddDictCellSigned: failed to build dict"

private def mkIAddStack
    (n : Int)
    (key : Value)
    (dict : Value := .null)
    (value : Builder := builderVal) : Array Value :=
  #[.builder value, key, dict, intV n]

private def mkIAddStackInt
    (n : Int)
    (key : Int)
    (dict : Value := .null)
    (value : Builder := builderVal) : Array Value :=
  mkIAddStack n (intV key) dict value

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIAddBId
    codeCell? := some dictIAddBCode
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
    instr := dictIAddBId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictIAddBDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSetB dictIAddBInstr stack

private def runDictIAddBDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSetB .add (VM.push (intV 1001)) stack

private def expectAssembleErr (name : String) (expected : Excno) (code : Instr) : IO Unit := do
  match assembleCp0 [code] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{name}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{name}: expected assemble failure")

private def expectAssembleOk16 (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c => do
      let rest ← expectDecodeStep label (Slice.ofCell c) instr 16
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected no trailing bits")
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr} with {bits} bits")

private def dictIAddExactGas : Int := computeExactGasBudget dictIAddBInstr
private def dictIAddExactGasMinusOne : Int := computeExactGasBudgetMinusOne dictIAddBInstr

private def opRawSlice16 (w : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w 16) #[])

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

private def randomKeyInRange (n : Nat) (rng0 : StdGen) : Int × StdGen :=
  if n = 0 then
    (0, rng0)
  else
    let lo := signedRangeMin n
    let hi := signedRangeMax n
    let (mode, rng1) := randNat rng0 0 6
    if mode = 0 then
      (lo, rng1)
    else if mode = 1 then
      (hi, rng1)
    else if mode = 2 then
      (0, rng1)
    else if mode = 3 then
      (hi / 2, rng1)
    else if mode = 4 then
      (lo / 2, rng1)
    else if mode = 5 then
      (1, rng1)
    else
      (-1, rng1)

private def randomKeyOutOfRange (n : Nat) (rng0 : StdGen) : Int × StdGen :=
  if n = 0 then
    (1, rng0)
  else
    let lo := signedRangeMin n
    let hi := signedRangeMax n
    let (mode, rng1) := randNat rng0 0 2
    if mode = 0 then
      (hi + 1, rng1)
    else if mode = 1 then
      (lo - 1, rng1)
    else
      (hi + 2, rng1)

private def genDICTIADDBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  if shape = 0 then
    (mkCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 1 then
    (mkCase "fuzz/underflow/one" #[intV 7], rng1)
  else if shape = 2 then
    (mkCase "fuzz/underflow/two" #[intV 1, .cell Cell.empty], rng1)
  else if shape = 3 then
    (mkCase "fuzz/underflow/three" #[.builder builderVal, intV 7, .null], rng1)
  else
    let (n, rng2) := pickNForFuzz rng1
    let (inRangeKey, rng3) := randomKeyInRange n rng2
    let (outRangeKey, rng4) := randomKeyOutOfRange n rng3
    let dictCell : Value := .cell (mkDictCellSigned n inRangeKey)
    let nI : Int := Int.ofNat n
    if shape = 4 then
      (mkCase "fuzz/ok/existing" (mkIAddStackInt nI inRangeKey dictCell), rng4)
    else if shape = 5 then
      (mkCase "fuzz/ok/miss" (mkIAddStackInt nI outRangeKey .null), rng4)
    else if shape = 6 then
      (mkCase "fuzz/err/key-out-of-range" (mkIAddStackInt nI outRangeKey .null), rng4)
    else if shape = 7 then
      ( { name := "fuzz/err/key-nan"
          instr := dictIAddBId
          program := #[.pushInt .nan, .xchg0 1, .xchg 1 2, dictIAddBInstr]
          initStack := #[.builder builderVal, .null, intV nI]
          fuel := 1_000_000 }
      , rng4)
    else if shape = 8 then
      (mkCase "fuzz/err/n-too-large" (mkIAddStackInt 1024 0 .null), rng4)
    else if shape = 9 then
      (mkCase "fuzz/err/type-dict" (mkIAddStackInt nI inRangeKey (.int (.num 7))), rng4)
    else if shape = 10 then
      (mkCase "fuzz/err/type-key" (mkIAddStack nI .null dictCell), rng4)
    else
      (mkCaseCode "fuzz/error/malformed-dict" (mkIAddStackInt nI inRangeKey (.cell malformedDict)) malformedDict, rng4)


def suite : InstrSuite where
  id := dictIAddBId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack
          "dispatch-fallback"
          (runDictIAddBDispatchFallback #[])
          #[intV 1001] },
    { name := "unit/runtime/miss-inserted-dict"
      run := do
        expectOkStack
          "runtime/miss-null"
          (runDictIAddBDirect (mkIAddStackInt 4 3 .null))
          #[.cell (mkAddDictCellSigned 4 3), intV (-1)] },
    { name := "unit/runtime/hit-existing-key"
      run := do
        let root := mkDictCellSigned 4 3
        expectOkStack
          "runtime/hit"
          (runDictIAddBDirect (mkIAddStackInt 4 3 (.cell root)))
          #[.cell root, intV 0] },
    { name := "unit/runtime/underflow"
      run := do
        expectErr "runtime/underflow-empty" (runDictIAddBDirect #[]) .stkUnd
        expectErr "runtime/underflow-one" (runDictIAddBDirect #[.builder builderVal]) .stkUnd
        expectErr "runtime/underflow-two" (runDictIAddBDirect #[.builder builderVal, intV 0]) .stkUnd
        expectErr "runtime/underflow-three"
          (runDictIAddBDirect #[.builder builderVal, intV 0, .null]) .stkUnd },
    { name := "unit/runtime/n-constraints"
      run := do
        expectErr "runtime/n-not-int" (runDictIAddBDirect #[.builder builderVal, intV 0, .cell (mkDictCellSigned 1 0), .null]) .typeChk
        expectErr "runtime/n-nan" (runDictIAddBDirect #[.builder builderVal, intV 0, .null, .int .nan]) .rangeChk
        expectErr "runtime/n-negative" (runDictIAddBDirect (mkIAddStackInt (-1) 0 .null)) .rangeChk
        expectErr "runtime/n-too-large" (runDictIAddBDirect (mkIAddStackInt 1024 0 .null)) .rangeChk
        expectErr "runtime/n-zero-with-key-nonzero" (runDictIAddBDirect (mkIAddStackInt 0 1 .null)) .rangeChk },
    { name := "unit/runtime/type-checks"
      run := do
        expectErr "runtime/type-dict" (runDictIAddBDirect (mkIAddStackInt 5 0 (.int (.num 7))) ) .typeChk
        expectErr "runtime/key-not-int" (runDictIAddBDirect (mkIAddStack 5 (.null) (.cell (mkDictCellSigned 5 0)))) .typeChk
        expectErr "runtime/type-value" (runDictIAddBDirect #[intV 1, intV 5, .cell (mkDictCellSigned 5 0), intV 5]) .typeChk
        expectErr "runtime/key-nan" (runDictIAddBDirect (mkIAddStack 5 (.int .nan) (.cell (mkDictCellSigned 5 0)))) .rangeChk
        expectErr "runtime/key-out-of-range" (runDictIAddBDirect (mkIAddStackInt 5 16 (.null))) .rangeChk
        expectErr "runtime/dict-err" (runDictIAddBDirect (mkIAddStackInt 4 0 (.cell malformedDict))) .dictErr },
    { name := "unit/assembler-decode"
      run := do
        expectAssembleOk16 "assemble/iadb" (.dictSetB true false .add)
        expectAssembleOk16 "assemble/uadb" (.dictSetB true true .add)
        let _ ← expectDecodeStep "decode/iadb" (opRawSlice16 0xf452) (.dictSetB true false .add) 16
        let _ ← expectDecodeStep "decode/adb" (opRawSlice16 0xf451) (.dictSetB false false .add) 16
        let _ ← expectDecodeStep "decode/uadb" (opRawSlice16 0xf453) (.dictSetB true true .add) 16
        expectDecodeInvOpcode "decode/invalid-lower" dictADDBLowerInvalid
        expectDecodeInvOpcode "decode/invalid-upper" dictADDBUpperInvalid
        expectDecodeInvOpcode "decode/truncated-8" (Cell.mkOrdinary (natToBits 0xf452 8) #[]) },
    { name := "unit/gas-boundaries"
      run := do
        let exactRes := runDictIAddBDirect (mkIAddStackInt 4 3 (.cell (mkDictCellSigned 4 3)))
        expectOkStack
          "gas/hit-path"
          exactRes
          #[.cell (mkDictCellSigned 4 3), intV 0]
      }
  ]
  oracle := #[
    -- [B2] add-miss cases.
    mkCase "ok/miss/n0-key-0" (mkIAddStackInt 0 0 .null),
    mkCase "ok/miss/n1-key-0" (mkIAddStackInt 1 0 .null),
    mkCase "ok/miss/n1-key-1" (mkIAddStackInt 1 1 .null),
    mkCase "ok/miss/n2-key-3" (mkIAddStackInt 2 3 .null),
    mkCase "ok/miss/n4-key-7" (mkIAddStackInt 4 7 .null),
    mkCase "ok/miss/n5-key-neg2" (mkIAddStackInt 5 (-2) .null),
    mkCase "ok/miss/n8-key-127" (mkIAddStackInt 8 127 .null),
    mkCase "ok/miss/n16-key-1" (mkIAddStackInt 16 1 .null),

    -- [B3] add-hit cases.
    mkCase "ok/hit/n0-key0" (mkIAddStackInt 0 0 (.cell (mkDictCellSigned 0 0))),
    mkCase "ok/hit/n1-key0" (mkIAddStackInt 1 0 (.cell (mkDictCellSigned 1 0))),
    mkCase "ok/hit/n1-key-1" (mkIAddStackInt 1 (-1) (.cell (mkDictCellSigned 1 (-1)))),
    mkCase "ok/hit/n4-key3" (mkIAddStackInt 4 3 (.cell (mkDictCellSigned 4 3))),
    mkCase "ok/hit/n5-key-max" (mkIAddStackInt 5 (signedRangeMax 5) (.cell (mkDictCellSigned 5 (signedRangeMax 5)))),
    mkCase "ok/hit/n5-key-min" (mkIAddStackInt 5 (signedRangeMin 5) (.cell (mkDictCellSigned 5 (signedRangeMin 5)))),

    -- [B4] underflow branch.
    mkCase "err/underflow/empty" #[],
    mkCase "err/underflow/one" #[.builder builderVal],
    mkCase "err/underflow/two" #[.builder builderVal, intV 1],
    mkCase "err/underflow/three" #[.builder builderVal, intV 1, .cell Cell.empty],

    -- [B5] n/key/type validation branches.
    mkCase "err/n-not-int" (#[.builder builderVal, intV 1, .cell (mkDictCellSigned 1 0), .null]),
    { name := "err/n-nan"
      instr := dictIAddBId
      program := #[.pushInt .nan, dictIAddBInstr]
      initStack := #[.builder builderVal, intV 1, .null]
      fuel := 1_000_000 },
    mkCase "err/n-negative" (mkIAddStackInt (-1) 1 .null),
    mkCase "err/n-too-large" (mkIAddStackInt 1024 0 .null),
    mkCase "err/key-not-int" (mkIAddStack 4 .null (.cell (mkDictCellSigned 4 3))),
    { name := "err/key-nan"
      instr := dictIAddBId
      program := #[.pushInt .nan, .xchg0 1, .xchg 1 2, dictIAddBInstr]
      initStack := #[.builder builderVal, .cell (mkDictCellSigned 4 3), intV 4]
      fuel := 1_000_000 },
    mkCase "err/key-out-of-range-high" (mkIAddStackInt 4 16 .null),
    mkCase "err/key-out-of-range-low" (mkIAddStackInt 4 (-17) .null),
    mkCase "err/key-nonzero-for-n0" (mkIAddStackInt 0 1 .null),
    mkCase "err/type-dict" (mkIAddStackInt 4 1 (.int (.num 7))),
    mkCase "err/type-value" (#[intV 1, intV 2, .cell (mkDictCellSigned 4 1), intV 4]),

    -- [B6] malformed dictionary path.
    mkCase "err/dict/structurally-malformed" (mkIAddStackInt 4 1 (.cell malformedDict)),

    -- [B8] decode opcode coverage via raw cells.
    mkCaseCode "decode/iadb" (mkIAddStackInt 4 1 .null) dictIAddBCode,
    mkCaseCode "decode/adb" (mkIAddStackInt 4 1 .null) dictIAddBCodeADDB,
    mkCaseCode "decode/uadb" (mkIAddStackInt 4 1 .null) dictIAddBCodeUADDB,
    mkCaseCode "decode/invalid-lower" #[] dictADDBLowerInvalid,
    mkCaseCode "decode/invalid-upper" #[] dictADDBUpperInvalid,

    -- [B9] gas exactness (hit/no-create branch for deterministic cost).
    mkCase
      "gas/exact-hit-succeeds"
      (mkIAddStackInt 4 3 (.cell (mkDictCellSigned 4 3)))
      { gasLimit := dictIAddExactGas, gasMax := dictIAddExactGas, gasCredit := 0 },
    mkCase
      "gas/exact-minus-one-fails"
      (mkIAddStackInt 4 3 (.cell (mkDictCellSigned 4 3)))
      { gasLimit := dictIAddExactGasMinusOne, gasMax := dictIAddExactGasMinusOne, gasCredit := 0 }
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictIAddBId
      count := 500
      gen := genDICTIADDBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIADDB
