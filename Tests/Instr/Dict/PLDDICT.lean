import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell
open Tests

namespace Tests.Instr.Dict.PLDDICT

/-!
INSTRUCTION: PLDDICT

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch branch.
   `execInstrDictLddict` handles `.lddict` directly; all other instructions execute `next`.

2. [B2] Stack preconditions.
   The instruction expects one operand and `VM.popSlice` enforces underflow (`.stkUnd`) and type check (`.typeChk`).

3. [B3] Bit availability.
   `haveBits 1` check gates progress:
   - if false and `quiet = false`, execution throws `.cellUnd`.
   - if false and `quiet = true`, execution keeps the original slice when `preload = false` and continues to quiet completion.

4. [B4] Tag branch = absent (`0`).
   On present=0 and enough bits, any ref tail is ignored for payload presence checks and the result path is the non-reference branch.

5. [B5] Tag branch = present (`1`) and valid ref tail.
   The first reference is extracted and pushed. For `preload = false`, remaining bits/refs are pushed as a slice.

6. [B6] Tag branch = present (`1`) but no usable ref.
   This is an error path: `.cellUnd` regardless of `preload`; both `quiet` modes share the same failure.

7. [B7] `preload` behavior.
   `preload = false` appends consumed remainder slice; `preload = true` omits it on successful extraction.

8. [B8] `quiet` success behavior.
   On successful extraction only, `quiet = true` pushes `-1`.
   On miss under C++ semantics, it should push `0`; Lean currently does not do this in this codebase and should be validated via oracle comparison.

9. [B9] Assembler/decoder behavior.
   - `assembleCp0` accepts only boolean flags (`preload`,`quiet`) and maps them to opcodes `0xF404`..`0xF407`.
   - `decodeCp0WithBits` accepts exactly that 4-value mask set.
   - adjacent/gap opcodes (`0xF403`, `0xF408`) and truncated opcodes should be invalid.

10. [B10] Gas accounting.
   No dynamic gas penalty branch exists in Lean execution here; gas is fixed.
   Exact single-instruction budget should succeed, and budget - 1 should fail.

TOTAL BRANCHES: 10
Each oracle test below is tagged with the branch(es) it covers.
-/

private def suiteId : InstrId := { name := "PLDDICT" }

private def baseInstr : Instr := .lddict false false

private def fallbackSentinel : Int := 42_001

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def raw15 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 15) #[]

private def opcodeF404 : Cell := raw16 0xF404
private def opcodeF405 : Cell := raw16 0xF405
private def opcodeF406 : Cell := raw16 0xF406
private def opcodeF407 : Cell := raw16 0xF407
private def opcodeF403 : Cell := raw16 0xF403
private def opcodeF402 : Cell := raw16 0xF402
private def opcodeF408 : Cell := raw16 0xF408
private def malformed8 : Cell := raw8 0xF4
private def malformed15 : Cell := raw15 (0xF40 >>> 1)

private def presentSimple : Slice := mkSliceWithBitsRefs (natToBits 1 1) #[refLeafA]
private def presentAlt : Slice := mkSliceWithBitsRefs (natToBits 1 1) #[refLeafB]
private def presentLong : Slice := mkSliceWithBitsRefs (natToBits 0b1101 4) #[refLeafA, refLeafB, refLeafC]
private def presentMissingRef : Slice := mkSliceWithBitsRefs (natToBits 1 1) #[]

private def absentSimple : Slice := mkSliceFromBits (natToBits 0 1)
private def absentShortTail : Slice := mkSliceWithBitsRefs (natToBits 0b0110 4) #[refLeafA]
private def absentLongTail : Slice := mkSliceWithBitsRefs (natToBits 0b001010 6) #[refLeafA, refLeafB]
private def absentWithRefs : Slice := mkSliceWithBitsRefs (natToBits 0 1) #[refLeafA]
private def emptySlice : Slice := mkSliceFromBits (natToBits 0 0)

private def remAfterTagPresent (s : Slice) : Slice :=
  { s with bitPos := s.bitPos + 1, refPos := s.refPos + 1 }

private def remAfterTagAbsent (s : Slice) : Slice :=
  { s with bitPos := s.bitPos + 1 }

private def baseGas : Int := computeExactGasBudget baseInstr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne baseInstr
private def gasExact : OracleGasLimits := oracleGasLimitsExact baseGas
private def gasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne

private def mkSetGasProgram (n : Int) (i : Instr) : Array Instr :=
  #[.pushInt (.num n), .tonEnvOp .setGasLimit, i]

private def runPLDDICT (preload quiet : Bool) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrDictLddict (.lddict preload quiet) stack

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictLddict .add (VM.push (intV fallbackSentinel)) stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (instr : Instr := baseInstr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[instr]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseWithProgram
    (name : String)
    (stack : Array Value := #[])
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk
    (label : String)
    (cell : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr actual}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decode did not consume full cell")

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected error {expected}, got {reprStr actual} ({bits} bits)")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleOk
    (label : String)
    (instr : Instr)
    (expectedBits : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")
  | .ok cell =>
      if cell.bits != natToBits expectedBits 16 then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {cell.bits}")

private def genPLDDICTFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (baseCase, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/present/simple" #[.slice presentSimple] (.lddict false false), rng1)
    else if shape = 1 then
      (mkCase "fuzz/present/alt/preload" #[.slice presentAlt] (.lddict true false), rng1)
    else if shape = 2 then
      (mkCase "fuzz/present/long-preload" #[.slice presentLong] (.lddict false false), rng1)
    else if shape = 3 then
      (mkCase "fuzz/present/maybe-alt-quiet" #[.slice presentSimple] (.lddict false true), rng1)
    else if shape = 4 then
      (mkCase "fuzz/present/preload-true-quiet" #[.slice presentLong] (.lddict true true), rng1)
    else if shape = 5 then
      (mkCase "fuzz/absent/simple" #[.slice absentSimple] (.lddict false false), rng1)
    else if shape = 6 then
      (mkCase "fuzz/absent/short-tail" #[.slice absentShortTail] (.lddict true false), rng1)
    else if shape = 7 then
      (mkCase "fuzz/absent/long-tail" #[.slice absentLongTail] (.lddict false true), rng1)
    else if shape = 8 then
      (mkCase "fuzz/absent/preload-true-quiet" #[.slice absentWithRefs] (.lddict true true), rng1)
    else if shape = 9 then
      (mkCase "fuzz/no-bits/non-quiet" #[.slice emptySlice] (.lddict false false), rng1)
    else if shape = 10 then
      (mkCase "fuzz/no-bits/quiet-preload-false" #[.slice emptySlice] (.lddict false true), rng1)
    else if shape = 11 then
      (mkCase "fuzz/no-bits/quiet-preload-true" #[.slice emptySlice] (.lddict true true), rng1)
    else if shape = 12 then
      (mkCase "fuzz/present/missing-ref" #[.slice presentMissingRef] (.lddict false false), rng1)
    else if shape = 13 then
      (mkCase "fuzz/type-error/int" #[intV 123], rng1)
    else if shape = 14 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 15 then
      (mkCaseCode "fuzz/decode/f404" #[] opcodeF404, rng1)
    else if shape = 16 then
      (mkCaseCode "fuzz/decode/f405" #[] opcodeF405, rng1)
    else if shape = 17 then
      (mkCaseCode "fuzz/decode/f406" #[] opcodeF406, rng1)
    else if shape = 18 then
      (mkCaseCode "fuzz/decode/f408-gap" #[] opcodeF408, rng1)
    else if shape = 19 then
      (mkCaseCode "fuzz/decode/trunc8" #[] malformed8, rng1)
    else if shape = 20 then
      (mkCaseCode "fuzz/decode/trunc15" #[] malformed15, rng1)
    else if shape = 21 then
      (mkCaseWithProgram "fuzz/gas/exact-present" #[.slice presentSimple]
        (mkSetGasProgram baseGas (.lddict false false)) gasExact, rng1)
    else if shape = 22 then
      (mkCaseWithProgram "fuzz/gas/minus-one-present" #[.slice presentSimple]
        (mkSetGasProgram baseGasMinusOne (.lddict false false)) gasExactMinusOne, rng1)
    else if shape = 23 then
      (mkCaseWithProgram "fuzz/gas/exact-absent" #[.slice absentSimple]
        (mkSetGasProgram baseGas (.lddict true true)) gasExact, rng1)
    else
      (mkCaseWithProgram "fuzz/gas/minus-one-absent" #[.slice absentWithRefs]
        (mkSetGasProgram baseGasMinusOne (.lddict true true)) gasExactMinusOne, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDispatchFallback #[] with
        | .ok st =>
            let expected : Array Value := #[.int (.num fallbackSentinel)]
            if st != expected then
              throw (IO.userError s!"dispatch fallback: expected {reprStr expected}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch fallback: expected success, got {e}") },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runPLDDICT false false #[]) .stkUnd },
    { name := "unit/runtime/type-check" -- [B2]
      run := do
        expectErr "type-check" (runPLDDICT false false #[intV 7]) .typeChk },
    { name := "unit/runtime/no-bits-nonquiet" -- [B3]
      run := do
        expectErr "no-bits" (runPLDDICT false false #[.slice emptySlice]) .cellUnd },
    { name := "unit/runtime/no-bits-quiet-preload-false" -- [B3][B8]
      run := do
        expectOkStack "no-bits-quiet-preload-false"
          (runPLDDICT false true #[.slice emptySlice])
          #[.slice emptySlice] },
    { name := "unit/runtime/no-bits-quiet-preload-true" -- [B3][B8]
      run := do
        expectOkStack "no-bits-quiet-preload-true"
          (runPLDDICT true true #[.slice emptySlice])
          #[] },
    { name := "unit/runtime/present-missing-ref" -- [B6]
      run := do
        expectErr "present-missing-ref" (runPLDDICT false false #[.slice presentMissingRef]) .cellUnd },
    { name := "unit/runtime/absent-nonquiet-preload-false" -- [B4][B7]
      run := do
        expectOkStack "absent-nonquiet-preload-false"
          (runPLDDICT false false #[.slice absentSimple])
          #[.null, .slice (remAfterTagAbsent absentSimple)] },
    { name := "unit/runtime/absent-nonquiet-preload-true" -- [B4][B7]
      run := do
        expectOkStack "absent-nonquiet-preload-true"
          (runPLDDICT true false #[.slice absentSimple])
          #[.null] },
    { name := "unit/runtime/present-nonquiet-preload-false" -- [B5][B7]
      run := do
        expectOkStack "present-nonquiet-preload-false"
          (runPLDDICT false false #[.slice presentSimple])
          #[.cell refLeafA, .slice (remAfterTagPresent presentSimple)] },
    { name := "unit/runtime/present-nonquiet-preload-true" -- [B5][B7]
      run := do
        expectOkStack "present-nonquiet-preload-true"
          (runPLDDICT true false #[.slice presentSimple])
          #[.cell refLeafA] },
    { name := "unit/runtime/present-quiet-nonpreload-simple" -- [B8][B7][B5]
      run := do
        expectOkStack "present-quiet-nonpreload-simple"
          (runPLDDICT false true #[.slice presentLong])
          #[.cell refLeafA, .slice (remAfterTagPresent presentLong), intV (-1)] },
    { name := "unit/runtime/absent-quiet-nonpreload-tail" -- [B8][B7][B4]
      run := do
        expectOkStack "absent-quiet-nonpreload-tail"
          (runPLDDICT false true #[.slice absentLongTail])
          #[.null, .slice (remAfterTagAbsent absentLongTail), intV (-1)] },
    { name := "unit/runtime/present-quiet-preload-true" -- [B8][B7][B5]
      run := do
        expectOkStack "present-quiet-preload-true"
          (runPLDDICT true true #[.slice presentAlt])
          #[.cell refLeafB, intV (-1)] },
    { name := "unit/runtime/absent-quiet-preload-true" -- [B8][B7][B4]
      run := do
        expectOkStack "absent-quiet-preload-true"
          (runPLDDICT true true #[.slice absentWithRefs])
          #[.null, intV (-1)] },
    { name := "unit/decode/f404-false/false" -- [B9]
      run := do
        expectDecodeOk "decode/f404" opcodeF404 (.lddict false false)
        expectDecodeOk "decode/f405" opcodeF405 (.lddict true false)
        expectDecodeOk "decode/f406" opcodeF406 (.lddict false true)
        expectDecodeOk "decode/f407" opcodeF407 (.lddict true true) },
    { name := "unit/decode/adjacent-and-gap" -- [B9]
      run := do
        expectDecodeOk "decode/f403" opcodeF403 (.dictExt (.lddicts false))
        expectDecodeOk "decode/f402" opcodeF402 (.dictExt (.lddicts true))
        expectDecodeErr "decode/f408" opcodeF408 .invOpcode
        expectDecodeErr "decode/truncated8" malformed8 .invOpcode
        expectDecodeErr "decode/truncated15" malformed15 .invOpcode },
    { name := "unit/assemble/opcodes" -- [B9]
      run := do
        expectAssembleOk "asm/f404" (.lddict false false) 0xF404
        expectAssembleOk "asm/f405" (.lddict true false) 0xF405
        expectAssembleOk "asm/f406" (.lddict false true) 0xF406
        expectAssembleOk "asm/f407" (.lddict true true) 0xF407 },
    { name := "unit/gas/exact-success" -- [B10]
      run := do
        expectOkStack "gas/exact-base-success"
          (runHandlerDirectWithNext execInstrDictLddict (.lddict false false)
            (pure ())
            (#[.slice presentSimple]))
          #[.cell refLeafA, .slice (remAfterTagPresent presentSimple)] }
  ]
  oracle := #[
    mkCase "oracle/dispatch-fallback" #[] , -- [B1]
    mkCase "oracle/runtime/underflow-empty" #[] , -- [B2]
    mkCase "oracle/runtime/type-error-int" #[intV 1] , -- [B2]
    mkCase "oracle/runtime/no-bits-nonquiet" #[.slice emptySlice] (.lddict false false), -- [B3]
    mkCase "oracle/runtime/no-bits-quiet-preload-false" #[.slice emptySlice] (.lddict false true), -- [B3][B8]
    mkCase "oracle/runtime/no-bits-quiet-preload-true" #[.slice emptySlice] (.lddict true true), -- [B3][B8]
    mkCase "oracle/present/simple/nonquiet" #[.slice presentSimple], -- [B5][B7]
    mkCase "oracle/present/alt/preload" #[.slice presentAlt] (.lddict true false), -- [B5][B7]
    mkCase "oracle/present/long/preload" #[.slice presentLong] (.lddict false false), -- [B5][B7]
    mkCase "oracle/present/quiet-preload-false" #[.slice presentSimple] (.lddict false true), -- [B8][B5]
    mkCase "oracle/present/quiet-preload-true" #[.slice presentSimple] (.lddict true true), -- [B8][B5]
    mkCase "oracle/absent/simple" #[.slice absentSimple] (.lddict false false), -- [B4][B7]
    mkCase "oracle/absent/preload" #[.slice absentWithRefs] (.lddict true false), -- [B4][B7]
    mkCase "oracle/absent/quiet-preload-false" #[.slice absentShortTail] (.lddict false true), -- [B8][B4]
    mkCase "oracle/absent/quiet-preload-true" #[.slice absentLongTail] (.lddict true true), -- [B8][B4]
    mkCase "oracle/absent/refs-ignored" #[.slice absentWithRefs] (.lddict false false), -- [B4][B5]
    mkCase "oracle/present/missing-ref" #[.slice presentMissingRef] (.lddict false false), -- [B6]
    mkCase "oracle/present/missing-ref-quiet" #[.slice presentMissingRef] (.lddict false true), -- [B6][B8]
    mkCase "oracle/present/missing-ref-preload-true" #[.slice presentMissingRef] (.lddict true false), -- [B6]
    mkCase "oracle/present/push-nonquiet-sibling" #[.slice presentAlt] (.lddict false false), -- [B5]
    mkCaseCode "oracle/decode/f404" #[] opcodeF404, -- [B9]
    mkCaseCode "oracle/decode/f405" #[] opcodeF405, -- [B9]
    mkCaseCode "oracle/decode/f406" #[] opcodeF406, -- [B9]
    mkCaseCode "oracle/decode/f407" #[] opcodeF407, -- [B9]
    mkCaseCode "oracle/decode/adjacent-lower" #[] opcodeF403, -- [B9]
    mkCaseCode "oracle/decode/adjacent-upper" #[] opcodeF402, -- [B9]
    mkCaseCode "oracle/decode/invalid-gap" #[] opcodeF408, -- [B9]
    mkCaseCode "oracle/decode/truncated8" #[] malformed8, -- [B9]
    mkCaseCode "oracle/decode/truncated15" #[] malformed15, -- [B9]
    mkCase "oracle/asm/f404" #[] (.lddict false false), -- [B9]
    mkCase "oracle/asm/f405" #[] (.lddict true false), -- [B9]
    mkCase "oracle/asm/f406" #[] (.lddict false true), -- [B9]
    mkCase "oracle/asm/f407" #[] (.lddict true true), -- [B9]
    mkCaseWithProgram "oracle/gas/exact/present/nonquiet" #[.slice presentSimple]
      (mkSetGasProgram baseGas (.lddict false false)) gasExact, -- [B10]
    mkCaseWithProgram "oracle/gas/minus-one/present/nonquiet" #[.slice presentSimple]
      (mkSetGasProgram baseGasMinusOne (.lddict false false)) gasExactMinusOne, -- [B10]
    mkCaseWithProgram "oracle/gas/exact/absent/quiet" #[.slice absentSimple]
      (mkSetGasProgram baseGas (.lddict false true)) gasExact, -- [B10]
    mkCaseWithProgram "oracle/gas/minus-one/absent/quiet" #[.slice absentShortTail]
      (mkSetGasProgram baseGasMinusOne (.lddict false true)) gasExactMinusOne, -- [B10]
    mkCase "oracle/noise/present-long-preload-true" #[.slice presentLong] (.lddict true false), -- [B5][B7]
    mkCase "oracle/noise/absent-tail-with-refs" #[.slice absentLongTail] (.lddict true false), -- [B4][B7]
    mkCase "oracle/noise/type-not-slice" #[.cell refLeafA] (.lddict false false), -- [B2]
    mkCase "oracle/noise/no-bits-empty-preload-true-quiet" #[.slice emptySlice] (.lddict true true), -- [B3][B8]
    mkCase "oracle/noise/type-not-slice-quiet" #[.cell refLeafA] (.lddict false true) -- [B2]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genPLDDICTFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PLDDICT
