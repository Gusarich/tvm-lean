import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PLDDICTS

/-!
INSTRUCTION: PLDDICTS

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch/runtime selection:
   `execInstrDictExt` handles `.dictExt (.lddicts true)`.
   Non-matching instructions defer to `next`.

2. [B2] Operand fetching:
   - `.stkUnd` when no operand is available.
   - `.typeChk` when top-of-stack is not a slice.

3. [B3] Input shape validation:
   - empty/malformed slice payload (`haveBits 1` fails) -> `.cellUnd`.
   - first bit `1` with missing required ref (`haveRefs 1` fails) -> `.cellUnd`.

4. [B4] Prefix/bit extraction:
   - `present = true` pushes one-bit prefix slice with the first reference.
   - `present = false` pushes `.null`.
   - prefix extraction is based on first bit only.

5. [B5] Assembler encoding:
   `.dictExt (.lddicts true)` and `.dictExt (.lddicts false)` are encodable by CP0.
   Assembly roundtrips through `decodeCp0WithBits` with 16-bit encoding.

6. [B6] Decoder behavior:
   - `0xf403` decodes to `.dictExt (.lddicts true)`.
   - `0xf402` decodes to `.dictExt (.lddicts false)`.
   - `0xf404` decodes to `.lddict false false` and must not be interpreted as PLDDICTS.
   - 8-bit and 15-bit truncations are decoder errors (`.invOpcode`).

7. [B7] Gas accounting:
   PLDDICTS has fixed instruction gas for successful execution in this implementation.
   `computeExactGasBudget` must match exact and exact-minus-one boundary behavior.

8. [B8] Reference robustness:
   if extra refs are present with `present = 1`, only the first ref in the prefix slice is surfaced.

9. [B9] Preload semantics:
   no remainder slice is pushed; only one result is pushed.

TOTAL BRANCHES: 9
Each oracle test below is tagged with one or more branch IDs.
-/

private def pldDictsId : InstrId :=
  { name := "PLDDICTS" }

private def pldDictsInstr : Instr :=
  .dictExt (.lddicts true)

private def fallbackSentinel : Int :=
  9_000_007

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def raw15 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 15) #[]

private def pldDictsCode : Cell :=
  raw16 0xf403

private def lddictsCode : Cell :=
  raw16 0xf402

private def lddictCode : Cell :=
  raw16 0xf404

private def malformed8 : Cell :=
  raw8 0xf4

private def malformed15 : Cell :=
  raw15 (0xf403 >>> 1)

private def valueCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[]

private def valueCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x5A 8) #[]

private def valueCellC : Cell :=
  Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def presentPrefixA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[valueCellA])

private def presentPrefixB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[valueCellB])

private def presentPrefixC : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[valueCellC])

private def presentSliceA : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[valueCellA]

private def presentSliceB : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[valueCellB]

private def presentSliceC : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[valueCellC]

private def presentSliceWithExtraRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[valueCellA, valueCellB]

private def presentSliceLong : Slice :=
  mkSliceWithBitsRefs (natToBits 0b1011001 7) #[valueCellA, valueCellC]

private def presentSliceNoRef : Slice :=
  mkSliceFromBits (natToBits 1 1)

private def absentSliceSimple : Slice :=
  mkSliceFromBits (natToBits 0 1)

private def absentSliceWithTail : Slice :=
  mkSliceWithBitsRefs (natToBits 0b0101 4) #[valueCellA]

private def absentSliceWithTailManyBits : Slice :=
  mkSliceWithBitsRefs (natToBits 0b010101 6) #[valueCellA]

private def absentSliceWithRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0b000 3) #[valueCellA]

private def emptySlice : Slice :=
  mkSliceFromBits (natToBits 0 0)

private def pldDictsGas : Int :=
  computeExactGasBudget pldDictsInstr

private def pldDictsGasMinusOne : Int :=
  computeExactGasBudgetMinusOne pldDictsInstr

private def pldDictsGasExact : OracleGasLimits :=
  oracleGasLimitsExact pldDictsGas

private def pldDictsGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne pldDictsGasMinusOne

private def runPLDDICTS (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt pldDictsInstr stack

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV fallbackSentinel)) stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldDictsInstr])
    (gasLimits : OracleGasLimits := {}) : OracleCase :=
  { name := name
    instr := pldDictsId
    program := program
    initStack := stack
    gasLimits := gasLimits }

private def mkCodeCase
    (name : String)
    (stack : Array Value := #[])
    (code : Cell)
    (program : Array Instr := #[])
    (gasLimits : OracleGasLimits := {}) : OracleCase :=
  { name := name
    instr := pldDictsId
    codeCell? := some code
    program := program
    initStack := stack
    gasLimits := gasLimits }

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
        throw (IO.userError s!"{label}: expected end-of-stream decode")

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr actual} ({bits} bits)")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleExact
    (label : String)
    (instr : Instr)
    (w16 : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble ok, got {e}")
  | .ok c =>
      if c.bits != natToBits w16 16 then
        throw (IO.userError s!"{label}: expected bits {reprStr (natToBits w16 16)}, got {reprStr c.bits}")
      expectDecodeOk label c instr

private def mkProgramSetGas (n : Int) : Array Instr :=
  #[.pushInt (.num n), .tonEnvOp .setGasLimit, pldDictsInstr]

private def genPLDDICTSFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (baseCase, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/present-a" #[.slice presentSliceA], rng1)
    else if shape = 1 then
      (mkCase "fuzz/present-b" #[.slice presentSliceB], rng1)
    else if shape = 2 then
      (mkCase "fuzz/present-c" #[.slice presentSliceC], rng1)
    else if shape = 3 then
      (mkCase "fuzz/present-extra-refs" #[.slice presentSliceWithExtraRefs], rng1)
    else if shape = 4 then
      (mkCase "fuzz/present-long" #[.slice presentSliceLong], rng1)
    else if shape = 5 then
      (mkCase "fuzz/present-no-ref" #[.slice presentSliceNoRef], rng1)
    else if shape = 6 then
      (mkCase "fuzz/absent-simple" #[.slice absentSliceSimple], rng1)
    else if shape = 7 then
      (mkCase "fuzz/absent-tail" #[.slice absentSliceWithTail], rng1)
    else if shape = 8 then
      (mkCase "fuzz/absent-tail-many" #[.slice absentSliceWithTailManyBits], rng1)
    else if shape = 9 then
      (mkCase "fuzz/absent-with-refs" #[.slice absentSliceWithRefs], rng1)
    else if shape = 10 then
      (mkCase "fuzz/no-bits" #[.slice emptySlice], rng1)
    else if shape = 11 then
      (mkCase "fuzz/type-int" #[intV 7], rng1)
    else if shape = 12 then
      (mkCodeCase "fuzz/decode-valid" #[] pldDictsCode, rng1)
    else if shape = 13 then
      (mkCodeCase "fuzz/decode-lower" #[] lddictsCode, rng1)
    else if shape = 14 then
      (mkCodeCase "fuzz/decode-upper" #[] lddictCode, rng1)
    else if shape = 15 then
      (mkCase "fuzz/gas/exact/present" #[.slice presentSliceA] (mkProgramSetGas pldDictsGas) pldDictsGasExact, rng1)
    else if shape = 16 then
      (mkCase "fuzz/gas/exact-minus-one/present" #[.slice presentSliceA] (mkProgramSetGas pldDictsGasMinusOne) pldDictsGasExactMinusOne, rng1)
    else if shape = 17 then
      (mkCase "fuzz/gas/exact/absent" #[.slice absentSliceSimple] (mkProgramSetGas pldDictsGas) pldDictsGasExact, rng1)
    else if shape = 18 then
      (mkCase "fuzz/gas/exact-minus-one/absent" #[.slice absentSliceSimple] (mkProgramSetGas pldDictsGasMinusOne) pldDictsGasExactMinusOne, rng1)
    else if shape = 19 then
      (mkCodeCase "fuzz/decode-truncated8" #[] malformed8, rng1)
    else if shape = 20 then
      (mkCodeCase "fuzz/decode-truncated15" #[] malformed15, rng1)
    else if shape = 21 then
      (mkCase "fuzz/asm-false" #[.slice presentSliceA] #[.pushInt (.num pldDictsGas), .tonEnvOp .setGasLimit] pldDictsGasExact, rng1)
    else
      (mkCase "fuzz/fallback-stack" #[] , rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := pldDictsId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDispatchFallback #[] with
        | .ok stack =>
            if stack != #[intV fallbackSentinel] then
              throw (IO.userError s!"dispatch fallback: expected [sentinel], got {reprStr stack}")
        | .error e =>
            throw (IO.userError s!"dispatch fallback: expected success, got {e}") },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runPLDDICTS #[]) .stkUnd },
    { name := "unit/runtime/type-check" -- [B2]
      run := do
        expectErr "type-check" (runPLDDICTS #[intV 7]) .typeChk },
    { name := "unit/runtime/no-bit" -- [B3]
      run := do
        expectErr "no-bit" (runPLDDICTS #[.slice emptySlice]) .cellUnd },
    { name := "unit/runtime/present-missing-ref" -- [B3]
      run := do
        expectErr "present-missing-ref" (runPLDDICTS #[.slice presentSliceNoRef]) .cellUnd },
    { name := "unit/runtime/present-true-simple" -- [B4] [B8]
      run := do
        expectOkStack "present-true-simple" (runPLDDICTS #[.slice presentSliceA]) #[.slice presentPrefixA] },
    { name := "unit/runtime/present-true-extra-refs" -- [B4] [B8]
      run := do
        expectOkStack "present-true-extra-refs" (runPLDDICTS #[.slice presentSliceWithExtraRefs]) #[.slice presentPrefixA] },
    { name := "unit/runtime/present-true-different-value" -- [B4] [B8]
      run := do
        expectOkStack "present-true-different-value" (runPLDDICTS #[.slice presentSliceB]) #[.slice presentPrefixB] },
    { name := "unit/runtime/present-true-long" -- [B4] [B9]
      run := do
        expectOkStack "present-true-long" (runPLDDICTS #[.slice presentSliceLong]) #[.slice presentPrefixA] },
    { name := "unit/runtime/absent-simple" -- [B4]
      run := do
        expectOkStack "absent-simple" (runPLDDICTS #[.slice absentSliceSimple]) #[.slice absentSliceSimple] },
    { name := "unit/runtime/absent-tail" -- [B4]
      run := do
        expectOkStack "absent-tail" (runPLDDICTS #[.slice absentSliceWithTail]) #[.slice absentSliceSimple] },
    { name := "unit/runtime/absent-tail-many" -- [B4]
      run := do
        expectOkStack "absent-tail-many" (runPLDDICTS #[.slice absentSliceWithTailManyBits]) #[.slice absentSliceSimple] },
    { name := "unit/runtime/absent-with-refs" -- [B4]
      run := do
        expectOkStack "absent-with-refs" (runPLDDICTS #[.slice absentSliceWithRefs]) #[.slice absentSliceSimple] },
    { name := "unit/decode/valid-plddicts" -- [B6]
      run := do
        expectDecodeOk "decode-valid-plddicts" pldDictsCode (.dictExt (.lddicts true)) },
    { name := "unit/decode/valid-lddicts" -- [B6]
      run := do
        expectDecodeOk "decode-valid-lddicts" lddictsCode (.dictExt (.lddicts false)) },
    { name := "unit/decode/neighbor-is-not-lddicts" -- [B6]
      run := do
        expectDecodeOk "decode-neighbor" lddictCode (.lddict false false) },
    { name := "unit/decode/truncated-8" -- [B6]
      run := do
        expectDecodeErr "decode-truncated-8" malformed8 .invOpcode },
    { name := "unit/decode/truncated-15" -- [B6]
      run := do
        expectDecodeErr "decode-truncated-15" malformed15 .invOpcode },
    { name := "unit/asm/roundtrip-plddicts" -- [B5]
      run := do
        expectAssembleExact "asm/plddicts" pldDictsInstr 0xF403 },
    { name := "unit/asm/roundtrip-lddicts" -- [B5]
      run := do
        expectAssembleExact "asm/lddicts" (.dictExt (.lddicts false)) 0xF402 }
  ]
  oracle := #[
    mkCase "oracle/underflow-empty" #[] , -- [B2]
    mkCase "oracle/type-check" #[intV 7], -- [B2]
    mkCase "oracle/no-bit" #[.slice emptySlice], -- [B3]
    mkCase "oracle/present-missing-ref" #[.slice presentSliceNoRef], -- [B3]
    mkCase "oracle/present-simple-a" #[.slice presentSliceA], -- [B4] [B8] [B9]
    mkCase "oracle/present-simple-b" #[.slice presentSliceB], -- [B4] [B8]
    mkCase "oracle/present-simple-c" #[.slice presentSliceC], -- [B4] [B8]
    mkCase "oracle/present-extra-refs" #[.slice presentSliceWithExtraRefs], -- [B4] [B8]
    mkCase "oracle/present-long" #[.slice presentSliceLong], -- [B4] [B8] [B9]
    mkCase "oracle/absent-simple" #[.slice absentSliceSimple], -- [B4]
    mkCase "oracle/absent-tail" #[.slice absentSliceWithTail], -- [B4]
    mkCase "oracle/absent-tail-many" #[.slice absentSliceWithTailManyBits], -- [B4]
    mkCase "oracle/absent-with-refs" #[.slice absentSliceWithRefs], -- [B4]
    mkCase "oracle/stack-empty-with-tail" #[], -- [B2]
    mkCase "oracle/type-wrong-slice" #[.tuple #[] , .slice absentSliceSimple], -- [B2]
    mkCase "oracle/type-wrong-two" #[.tuple #[], .tuple #[]], -- [B2]
    mkCase "oracle/decode-valid" #[] (mkProgramSetGas pldDictsGas) pldDictsGasExact, -- [B6]
    mkCase "oracle/decode-valid-2" #[] (mkProgramSetGas pldDictsGas) pldDictsGasExact, -- [B6]
    mkCase "oracle/decode-lower-boundary" #[] (mkProgramSetGas pldDictsGas) pldDictsGasExact, -- [B6]
    mkCodeCase "oracle/code-plddicts" #[] pldDictsCode, -- [B6]
    mkCodeCase "oracle/code-lddicts" #[] lddictsCode, -- [B6]
    mkCodeCase "oracle/code-lddict" #[] lddictCode, -- [B6]
    mkCodeCase "oracle/code-trunc8" #[] malformed8, -- [B6]
    mkCodeCase "oracle/code-trunc15" #[] malformed15, -- [B6]
    mkCase "oracle/gas-exact/present" #[.slice presentSliceA] (mkProgramSetGas pldDictsGas) pldDictsGasExact, -- [B7]
    mkCase "oracle/gas-minus-one/present" #[.slice presentSliceA] (mkProgramSetGas pldDictsGasMinusOne) pldDictsGasExactMinusOne, -- [B7]
    mkCase "oracle/gas-exact/absent" #[.slice absentSliceSimple] (mkProgramSetGas pldDictsGas) pldDictsGasExact, -- [B7]
    mkCase "oracle/gas-minus-one/absent" #[.slice absentSliceSimple] (mkProgramSetGas pldDictsGasMinusOne) pldDictsGasExactMinusOne, -- [B7]
    mkCodeCase "oracle/replay-code-plddicts" #[] pldDictsCode (#[.pushInt (.num pldDictsGas), .tonEnvOp .setGasLimit]) pldDictsGasExact, -- [B6] [B7]
    mkCase "oracle/replay-presence-mix-a" #[.slice presentSliceB], -- [B4] [B8]
    mkCase "oracle/replay-presence-mix-c" #[.slice presentSliceC], -- [B4] [B8]
    mkCase "oracle/replay-absent-refs" #[.slice absentSliceWithRefs] -- [B4]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr pldDictsId
      count := 500
      gen := genPLDDICTSFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PLDDICTS
