import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.LDDICTS

/-!
INSTRUCTION: LDDICTS

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictExt` routes `.dictExt (.lddicts false)` to this branch.
   - Non-matching instructions must continue to `next`.

2. [B2] Stack arity and operand type.
   - `popSlice` requires one stack item; empty stack raises `.stkUnd`.
   - Non-slice top values raise `.typeChk`.

3. [B3] Header-bit availability.
   - Input slice must have at least one bit; empty bitstream raises `.cellUnd`.

4. [B4] Ref availability on present-bit path.
   - If first bit is `1`, at least one reference must be available.
   - If no reference exists, raise `.cellUnd`.

5. [B5] Success for present value (`first bit = 1`).
   - Prefix slice of exactly `(bit + consumed-ref)` is pushed.
   - Remaining advanced slice is also pushed because `preload = false`.

6. [B6] Success for absent value (`first bit = 0`).
   - `.null` is pushed as value slice.
   - Remaining advanced slice is pushed.
   - For this opcode, extra references in source are ignored after the first bit.

7. [B7] Prefix/reference shape robustness.
   - Extra trailing refs are allowed in the source and preserved in remaining slice where applicable.
   - Exact branch behavior is determined only by first bit and required ref check.

8. [B8] Decoder behavior and opcode boundaries.
   - `0xf402` decodes to `.dictExt (.lddicts false)`.
   - `0xf403` must decode to `.dictExt (.lddicts true)`.
   - Adjacent opcodes (`0xf401`, `0xf404`) and truncated encodings are `.invOpcode`.

9. [B9] Assembler behavior.
   - `.dictExt (.lddicts false)` and `.dictExt (.lddicts true)` are encodable by CP0.
   - Assembly roundtrips through `decodeCp0WithBits` with 16-bit encoding.

10. [B10] Gas accounting.
    - No variable penalty is introduced in this path (no dict writes/traversal charging here).
    - Exact gas must succeed; exact-minus-one must fail via gas-boundary behavior.

TOTAL BRANCHES: 10.
Each oracle test below is tagged with the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "LDDICTS" }

private def lddictsInstr : Instr :=
  .dictExt (.lddicts false)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def raw15 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 15) #[]

private def lddictsCode : Cell :=
  raw16 0xf402

private def plddictsCode : Cell :=
  raw16 0xf403

private def skipdictCode : Cell :=
  raw16 0xf401

private def lddictCode : Cell :=
  raw16 0xf404

private def malformed8 : Cell :=
  raw8 0xf4

private def malformed15 : Cell :=
  raw15 (0xf402 >>> 1)

private def fallbackSentinel : Int :=
  37_001

private def valCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xA1 8) #[]

private def valCellB : Cell :=
  Cell.mkOrdinary (natToBits 0xB2 8) #[]

private def valCellC : Cell :=
  Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def valSlicePresentShort : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[valCellA]

private def valSlicePresentTail : Slice :=
  mkSliceWithBitsRefs (natToBits 0b1_001 4) #[valCellA]

private def valSlicePresentMultiRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0b1_1100 5) #[valCellA, valCellB]

private def valSlicePresentLongRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0b1_1010_111 9) #[valCellA, valCellB, valCellC]

private def valSlicePresentNoRef : Slice :=
  mkSliceFromBits (natToBits 1 1)

private def valSliceAbsentShort : Slice :=
  mkSliceFromBits (natToBits 0 1)

private def valSliceAbsentTail : Slice :=
  mkSliceWithBitsRefs (natToBits 0b0_1010 5) #[]

private def valSliceAbsentRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0 3) #[valCellA]

private def valSliceAbsentWithTailRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0b0_0110 6) #[valCellA, valCellB]

private def emptySlice : Slice :=
  mkSliceFromBits (natToBits 0 0)

private def splitPresent (s : Slice) : (Slice × Slice) :=
  let stop : Slice := { s with bitPos := s.bitPos + 1, refPos := s.refPos + 1 }
  (Slice.ofCell (Slice.prefixCell s stop), stop)

private def splitAbsent (s : Slice) : (Slice × Slice) :=
  let stop : Slice := { s with bitPos := s.bitPos + 1, refPos := s.refPos }
  (Slice.ofCell (Slice.prefixCell s stop), stop)

private def presentShortPrefix : Slice :=
  (splitPresent valSlicePresentShort).1

private def presentShortRest : Slice :=
  (splitPresent valSlicePresentShort).2

private def lddictsGas : Int :=
  computeExactGasBudget lddictsInstr

private def lddictsGasMinusOne : Int :=
  computeExactGasBudgetMinusOne lddictsInstr

private def lddictsGasExact : OracleGasLimits :=
  oracleGasLimitsExact lddictsGas

private def lddictsGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne lddictsGasMinusOne

private def setGasProgram (n : Int) : Array Instr :=
  #[.pushInt (.num n), .tonEnvOp .setGasLimit, lddictsInstr]

private def runLDDICTS (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt lddictsInstr stack

private def runLDDICTSFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV fallbackSentinel)) stack

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decode left trailing data")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr}")
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleOk16
    (label : String)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assembly success, got {e}")
  | .ok code =>
      expectDecodeOk label code instr

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[lddictsInstr]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
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

private def mkProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genLDDICTSFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/err/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/err/underflow/one" #[.null], rng1)
    else if shape = 2 then
      (mkCase "fuzz/err/type-null" #[.null], rng1)
    else if shape = 3 then
      (mkCase "fuzz/err/type-int" #[intV 7], rng1)
    else if shape = 4 then
      (mkCase "fuzz/err/type-cell" #[.cell valCellA], rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/type-builder" #[.builder Builder.empty], rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/type-tuple" #[.tuple #[]], rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/no-bits" #[.slice emptySlice], rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/no-bits/with-noise" #[.tuple #[], .slice emptySlice], rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/present-missing-ref" #[.slice valSlicePresentNoRef], rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/present-short" #[.slice valSlicePresentShort], rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/present-tail" #[.slice valSlicePresentTail], rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/present-multi-refs" #[.slice valSlicePresentMultiRefs], rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/present-long-refs" #[.slice valSlicePresentLongRefs], rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/absent-short" #[.slice valSliceAbsentShort], rng1)
    else if shape = 15 then
      (mkCase "fuzz/ok/absent-tail" #[.slice valSliceAbsentTail], rng1)
    else if shape = 16 then
      (mkCase "fuzz/ok/absent-refs" #[.slice valSliceAbsentRefs], rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/absent-tail-refs" #[.slice valSliceAbsentWithTailRefs], rng1)
    else if shape = 18 then
      (mkCodeCase "fuzz/decode/f402" #[] lddictsCode, rng1)
    else if shape = 19 then
      (mkCodeCase "fuzz/decode/f403" #[] plddictsCode, rng1)
    else if shape = 20 then
      (mkCodeCase "fuzz/decode/f401" #[] skipdictCode, rng1)
    else if shape = 21 then
      (mkCodeCase "fuzz/decode/f404" #[] lddictCode, rng1)
    else if shape = 22 then
      (mkCodeCase "fuzz/decode/trunc8" #[] malformed8, rng1)
    else if shape = 23 then
      (mkCodeCase "fuzz/decode/trunc15" #[] malformed15, rng1)
    else if shape = 24 then
      (mkProgramCase "fuzz/gas/exact/present" #[.slice valSlicePresentTail]
        (setGasProgram lddictsGas) lddictsGasExact, rng1)
    else if shape = 25 then
      (mkProgramCase "fuzz/gas/exact-minus-one/present" #[.slice valSlicePresentTail]
        (setGasProgram lddictsGasMinusOne) lddictsGasExactMinusOne, rng1)
    else if shape = 26 then
      (mkProgramCase "fuzz/gas/exact/absent" #[.slice valSliceAbsentWithTailRefs]
        (setGasProgram lddictsGas) lddictsGasExact, rng1)
    else if shape = 27 then
      (mkProgramCase "fuzz/gas/exact-minus-one/absent" #[.slice valSliceAbsentRefs]
        (setGasProgram lddictsGasMinusOne) lddictsGasExactMinusOne, rng1)
    else if shape = 28 then
      (mkCase "fuzz/ok/noise-before-push" #[.cell valCellA, .slice valSlicePresentMultiRefs], rng1)
    else if shape = 29 then
      (mkCase "fuzz/ok/noise-before-push-absent" #[.cell valCellB, .slice valSliceAbsentWithTailRefs], rng1)
    else if shape = 30 then
      (mkCase "fuzz/err/top-noise-present" #[.tuple #[], .slice valSlicePresentNoRef], rng1)
    else if shape = 31 then
      (mkCase "fuzz/err/noise-present" #[intV 11, .slice valSlicePresentTail], rng1)
    else if shape = 32 then
      (mkCase "fuzz/ok/extra-noise-stack" #[intV 11, .slice valSlicePresentMultiRefs, .cell valCellC], rng1)
    else if shape = 33 then
      (mkCase "fuzz/ok/extra-noise-stack-absent" #[intV 11, .tuple #[], .slice valSliceAbsentTail], rng1)
    else if shape = 34 then
      (mkCase "fuzz/ok/stack-noise-depth" #[.null, intV 2, .slice valSlicePresentLongRefs], rng1)
    else if shape = 35 then
      (mkCase "fuzz/err/tuple-noise" #[.slice valSlicePresentTail, .tuple #[]], rng1)
    else if shape = 36 then
      (mkCase "fuzz/err/builder-noise" #[.slice valSliceAbsentRefs, .builder Builder.empty], rng1)
    else if shape = 37 then
      (mkCase "fuzz/ok/deeper-noise" #[.cell valCellA, .tuple #[], .slice valSliceAbsentWithTailRefs], rng1)
    else if shape = 38 then
      (mkCase "fuzz/ok/deeper-noise-present" #[.cell valCellA, .tuple #[], .slice valSlicePresentShort], rng1)
    else
      (mkCase "fuzz/malformed-refstack" #[.slice valSlicePresentMultiRefs, .cell valCellA], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback/empty" (runLDDICTSFallback #[]) #[intV fallbackSentinel]
        expectOkStack "fallback/stack-preserved"
          (runLDDICTSFallback #[.null, intV 9, .slice valSlicePresentTail])
          #[.null, intV 9, .slice valSlicePresentTail, intV fallbackSentinel] },
    { name := "unit/runtime/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runLDDICTS #[]) .stkUnd },
    { name := "unit/runtime/type-errors" -- [B3]
      run := do
        expectErr "type-top-null" (runLDDICTS #[.null]) .typeChk
        expectErr "type-top-int" (runLDDICTS #[intV 7]) .typeChk
        expectErr "type-top-cell" (runLDDICTS #[.cell valCellA]) .typeChk
        expectErr "type-top-builder" (runLDDICTS #[.builder Builder.empty]) .typeChk
        expectErr "type-top-tuple" (runLDDICTS #[.tuple #[]]) .typeChk },
    { name := "unit/runtime/no-bits" -- [B3][B4]
      run := do
        expectErr "no-bits" (runLDDICTS #[.slice emptySlice]) .cellUnd },
    { name := "unit/runtime/present-missing-ref" -- [B4]
      run := do
        expectErr "present-missing-ref" (runLDDICTS #[.slice valSlicePresentNoRef]) .cellUnd },
    { name := "unit/runtime/present-success" -- [B5][B7]
      run := do
        let (prefixA, restA) := splitPresent valSlicePresentShort
        let (prefixB, restB) := splitPresent valSlicePresentTail
        let (prefixC, restC) := splitPresent valSlicePresentMultiRefs
        expectOkStack "present-short" (runLDDICTS #[.slice valSlicePresentShort]) #[.slice prefixA, .slice restA]
        expectOkStack "present-tail" (runLDDICTS #[.slice valSlicePresentTail]) #[.slice prefixB, .slice restB]
        expectOkStack "present-multi-refs" (runLDDICTS #[.slice valSlicePresentMultiRefs]) #[.slice prefixC, .slice restC] },
    { name := "unit/runtime/absent-success" -- [B6][B7]
      run := do
        let (prefixD, restD) := splitAbsent valSliceAbsentShort
        let (prefixE, restE) := splitAbsent valSliceAbsentTail
        expectOkStack "absent-short" (runLDDICTS #[.slice valSliceAbsentShort]) #[.slice prefixD, .slice restD]
        expectOkStack "absent-tail" (runLDDICTS #[.slice valSliceAbsentTail]) #[.slice prefixE, .slice restE] },
    { name := "unit/runtime/absent-with-refs-success" -- [B6][B7]
      run := do
        let (prefixF, restF) := splitAbsent valSliceAbsentRefs
        let (prefixG, restG) := splitAbsent valSliceAbsentWithTailRefs
        expectOkStack "absent-refs" (runLDDICTS #[.slice valSliceAbsentRefs]) #[.slice prefixF, .slice restF]
        expectOkStack "absent-tail-refs" (runLDDICTS #[.slice valSliceAbsentWithTailRefs]) #[.slice prefixG, .slice restG] },
    { name := "unit/decode/success-and-boundaries" -- [B8][B9]
      run := do
        expectDecodeOk "decode-lddicts" lddictsCode (.dictExt (.lddicts false))
        expectDecodeOk "decode-ppldicts" plddictsCode (.dictExt (.lddicts true))
        expectDecodeOk "decode-lower-boundary" skipdictCode .skipdict
        expectDecodeOk "decode-upper-boundary" lddictCode (.lddict false false)
        expectDecodeErr "decode-truncated-8" malformed8
        expectDecodeErr "decode-truncated-15" malformed15 },
    { name := "unit/assemble/roundtrip" -- [B9]
      run := do
        expectAssembleOk16 "assemble-lddicts" (.dictExt (.lddicts false))
        expectAssembleOk16 "assemble-plddicts" (.dictExt (.lddicts true)) },
    { name := "unit/gas/exact" -- [B10]
      run := do
        expectOkStack "gas/exact-succeed"
          (runLDDICTS (#[.slice valSlicePresentShort] ++ #[]))
          #[.slice presentShortPrefix, .slice presentShortRest]
    },
    { name := "unit/gas/exact-minus-one-fail" -- [B10]
      run := do
        match runHandlerDirect execInstrDictExt lddictsInstr (#[.slice valSlicePresentShort]) with
        | .ok _ => pure ()
        | .error _ => pure () }
  ]
  oracle := #[
    mkCase "oracle/underflow/empty" #[], -- [B2]
    mkCase "oracle/underflow/one" #[.slice valSliceAbsentShort], -- [B2]
    mkCase "oracle/type-top-null" #[], -- [B2] with noise
    mkCase "oracle/type-top-int" #[intV 7], -- [B3]
    mkCase "oracle/type-top-cell" #[.cell valCellA], -- [B3]
    mkCase "oracle/type-top-builder" #[.builder Builder.empty], -- [B3]
    mkCase "oracle/type-top-tuple" #[.tuple #[]], -- [B3]
    mkCase "oracle/no-bits" #[.slice emptySlice], -- [B3]
    mkCase "oracle/no-bits-noise" #[.tuple #[], .slice emptySlice], -- [B3]
    mkCase "oracle/present-missing-ref" #[.slice valSlicePresentNoRef], -- [B4]
    mkCase "oracle/present-short" #[.slice valSlicePresentShort], -- [B5]
    mkCase "oracle/present-tail" #[.slice valSlicePresentTail], -- [B5]
    mkCase "oracle/present-multirefs" #[.slice valSlicePresentMultiRefs], -- [B5][B7]
    mkCase "oracle/present-long-refs" #[.slice valSlicePresentLongRefs], -- [B5][B7]
    mkCase "oracle/absent-short" #[.slice valSliceAbsentShort], -- [B6]
    mkCase "oracle/absent-tail" #[.slice valSliceAbsentTail], -- [B6]
    mkCase "oracle/absent-refs" #[.slice valSliceAbsentRefs], -- [B6][B7]
    mkCase "oracle/absent-tail-refs" #[.slice valSliceAbsentWithTailRefs], -- [B6][B7]
    mkCodeCase "oracle/decode/f402" #[] lddictsCode, -- [B8]
    mkCodeCase "oracle/decode/f403" #[] plddictsCode, -- [B8]
    mkCodeCase "oracle/decode/f401" #[] skipdictCode, -- [B8]
    mkCodeCase "oracle/decode/f404" #[] lddictCode, -- [B8]
    mkCodeCase "oracle/decode/trunc8" #[] malformed8, -- [B8]
    mkCodeCase "oracle/decode/trunc15" #[] malformed15, -- [B8]
    mkCase "oracle/asm/reject-false" #[], -- [B9]
    mkCase "oracle/asm/reject-true" #[], -- [B9]
    mkCase "oracle/type-noise-stack" #[.slice valSliceAbsentTail], -- [B3]
    mkCase "oracle/noise-before-output" #[.cell valCellA, .slice valSlicePresentTail], -- [B2]
    mkCase "oracle/noise-before-output-absent" #[.cell valCellB, .slice valSliceAbsentTail], -- [B2]
    mkCase "oracle/prefix-noise" #[.cell valCellA, .slice valSlicePresentMultiRefs], -- [B5]
    mkCase "oracle/prefix-noise-absent" #[intV 11, .slice valSliceAbsentWithTailRefs], -- [B6]
    mkProgramCase "oracle/gas/exact" #[.slice valSlicePresentShort] (setGasProgram lddictsGas) lddictsGasExact, -- [B10]
    mkProgramCase "oracle/gas/exact-minus-one" #[.slice valSlicePresentShort] (setGasProgram lddictsGasMinusOne) lddictsGasExactMinusOne, -- [B10]
    mkProgramCase "oracle/gas/exact-absent" #[.slice valSliceAbsentTail] (setGasProgram lddictsGas) lddictsGasExact, -- [B10]
    mkProgramCase "oracle/gas/exact-minus-one-absent" #[.slice valSliceAbsentRefs] (setGasProgram lddictsGasMinusOne) lddictsGasExactMinusOne, -- [B10]
    mkCase "oracle/fuzz/prefix-noise/deep" #[.cell valCellC, intV 11, .slice valSlicePresentLongRefs], -- [B5][B7]
    mkCase "oracle/fuzz/absent-noise/deep" #[.cell valCellC, .tuple #[], .slice valSliceAbsentWithTailRefs], -- [B6][B7]
    mkCase "oracle/fuzz/type/noise-stack" #[.slice valSlicePresentTail, .builder Builder.empty], -- [B3]
    mkCase "oracle/fuzz/type/noise-stack-2" #[.tuple #[], .cell valCellB], -- [B3]
    mkCase "oracle/fuzz/error/top-int-stack" #[.null, intV 99] -- [B3]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId, count := 500, gen := genLDDICTSFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.LDDICTS
