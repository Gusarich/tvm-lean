import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUDELGET

/-!
INSTRUCTION: DICTUDELGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch/runtime selection:
   - `execInstrDictExt` handles `.dictExt` only.
   - `.dictExt (.mutGet true true false .del)` must execute this handler.
   - Non-`.dictExt` instructions fall through to `next`.

2. [B2] Runtime underflow:
   - `VM.checkUnderflow 3` rejects stacks with fewer than 3 items.
   - Empty/partial stacks hit before any other parsing.

3. [B3] Runtime `n` validation:
   - `popNatUpTo 1023` accepts `n=1023`.
   - `.typeChk` for non-int `n`.
   - `.rangeChk` for `n<0` and `n>1023`.

4. [B4] Dictionary/value key extraction:
   - `dict` uses `popMaybeCell`, accepting `.null` or `.cell`.
   - key uses `popInt`, expecting signed integer for integer-key forms.
   - `.nan` key and non-int key throw `.rangeChk`/`.typeChk`.
   - `dictKeyBits? idx n true` governs unsigned key acceptance.

5. [B5] Unsigned key conversion behavior:
   - Lean throws `.rangeChk` when `dictKeyBits?` returns `none`.
   - C++ uses `integer_key(..., quiet=true)` and treats out-of-range unsigned keys as miss (`0`), not exceptions.
   - Coverage includes values that exercise both matching and non-matching key encodings.

6. [B6] Dict lookup-delete semantics:
   - `.dictExt (.mutGet ... .del)` calls delete-lookup.
   - Hit path pushes old value as slice and `-1`.
   - Miss path pushes only updated root and `0`.

7. [B7] Root-shape payload behavior (by-ref false):
   - Unlike `....REF`, slice payloads are always accepted as-is.
   - Bit-heavy / no-ref / two-ref payloads are returned unchanged on hit.

8. [B8] Malformed dictionary traversal:
   - Invalid dictionary node shape can fail before hit/miss result with `.cellUnd` or `.dictErr`.

9. [B9] Assembler:
   - `.dictExt` variants are unsupported by assembler and must return `.invOpcode`.

10. [B10] Decoder:
   - `DICTUDELGET` decodes from `0xf466`.
   - `0xf462..0xf467` is the whole DELGET family.
   - Neighbor decode checks:
     - `0xf465` => `DICTIDELGETREF`
     - `0xf467` => `DICTUDELGETREF`
   - `0xf461` and `0xf468` are boundary failures.
   - Truncated inputs fail decode with `.invOpcode`.

11. [B11] Gas accounting:
   - Base gas from instruction metadata (`computeExactGasBudget` + minus-one variant).
   - Exact-gas success and exact-minus-one failure branches are covered for deterministic miss paths.

TOTAL BRANCHES: 11
Each oracle test below is tagged with the branch(es) it covers.
-/

private def dictUdelGetId : InstrId :=
  { name := "DICTUDELGET" }

private def dictUdelGetInstr : Instr :=
  .dictExt (.mutGet true true false .del)

private def dictUdelGetCode : Cell :=
  Cell.mkOrdinary (natToBits 0xf466 16) #[]

private def rawCell16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def dictUdelGetNeighborSignedCode : Cell :=
  rawCell16 0xf465

private def dictUdelGetNeighborUnsignedRefCode : Cell :=
  rawCell16 0xf467

private def dictUdelGetNeighborLowerGap : Cell :=
  rawCell16 0xf461

private def dictUdelGetNeighborUpperGap : Cell :=
  rawCell16 0xf468

private def dispatchSentinel : Int := 9093

private def sampleCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def sampleCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x3b 8) #[]

private def sampleCellC : Cell :=
  Cell.mkOrdinary (natToBits 0x17 8) #[]

private def valueCellWithBits : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def valueCellNoRef : Cell :=
  Cell.mkOrdinary #[] #[]

private def valueCellTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[sampleCellA, sampleCellB]

private def valueSliceA : Slice :=
  mkSliceFromBits (natToBits 0x7 3)

private def valueSliceB : Slice :=
  mkSliceFromBits (natToBits 0x5 3)

private def valueSliceC : Slice :=
  mkSliceFromBits (natToBits 0x2 3)

private def valueSliceBits : Slice :=
  Slice.ofCell valueCellWithBits

private def valueSliceTwoRefs : Slice :=
  Slice.ofCell valueCellTwoRefs

private def malformedRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def keyBitsFor (idx : Int) (n : Nat) : BitString :=
  match dictKeyBits? idx n true with
  | some bs => bs
  | none =>
      panic! s!"expected key bits for idx={idx}, n={n}, unsigned=true"

private def mkDictSliceRoot (key : BitString) (value : Slice) : Cell :=
  match dictSetSliceWithCells none key value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _ok, _created, _loaded) =>
      panic! "failed to build single-entry dict root: insertion returned none"
  | .error e =>
      panic! s!"dictSetSliceWithCells failed: {reprStr e}"

private def mkDictSliceRoot2 (k1 : BitString) (v1 : Slice) (k2 : BitString) (v2 : Slice) : Cell :=
  match dictSetSliceWithCells none k1 v1 .set with
  | .ok (some root1, _ok1, _created1, _loaded1) =>
      match dictSetSliceWithCells (some root1) k2 v2 .set with
      | .ok (some root2, _ok2, _created2, _loaded2) => root2
      | .ok (none, _ok2, _created2, _loaded2) =>
          panic! "failed to build two-entry dict root: second insertion returned none"
      | .error e =>
          panic! s!"dictSetSliceWithCells failed: {reprStr e}"
  | .ok (none, _ok1, _created1, _loaded1) =>
      panic! "failed to build two-entry dict root: first insertion returned none"
  | .error e =>
      panic! s!"dictSetSliceWithCells failed: {reprStr e}"

private def uintRoot4Single0 : Cell :=
  mkDictSliceRoot (keyBitsFor 0 4) valueSliceA

private def uintRoot4Single15 : Cell :=
  mkDictSliceRoot (keyBitsFor 15 4) valueSliceB

private def uintRoot4Two : Cell :=
  mkDictSliceRoot2 (keyBitsFor 0 4) valueSliceA (keyBitsFor 15 4) valueSliceB

private def uintRoot4BadBits : Cell :=
  mkDictSliceRoot (keyBitsFor 9 4) valueSliceBits

private def uintRoot4BadNoRef : Cell :=
  mkDictSliceRoot (keyBitsFor 3 4) (mkSliceFromBits #[])

private def uintRoot4BadTwoRefs : Cell :=
  mkDictSliceRoot (keyBitsFor 11 4) valueSliceTwoRefs

private def uintRoot0 : Cell :=
  mkDictSliceRoot (keyBitsFor 0 0) valueSliceC

private def uintRoot8Single : Cell :=
  mkDictSliceRoot (keyBitsFor 0xA5 8) valueSliceB

private def mkIntCaseStack (root : Value) (key : Int) (n : Int) : Array Value :=
  #[root, intV key, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUdelGetId
    codeCell? := some dictUdelGetCode
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
    instr := dictUdelGetId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictUdelGetDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt dictUdelGetInstr stack

private def runDictUdelGetFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.tonEnvOp .setGasLimit) (VM.push (intV dispatchSentinel)) stack

private def dictUdelGetGas : Int :=
  computeExactGasBudget dictUdelGetInstr

private def dictUdelGetGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictUdelGetGas

private def dictUdelGetGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictUdelGetGas

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected end-of-stream decode")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {instr} ({bits} bits)")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembly error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def genDICTUDELGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    (mkCase (s! "fuzz/hit/single/0/{tag}") (mkIntCaseStack (.cell uintRoot4Single0) 0 4), rng2)
  else if shape = 1 then
    (mkCase (s! "fuzz/hit/single/15/{tag}") (mkIntCaseStack (.cell uintRoot4Single15) 15 4), rng2)
  else if shape = 2 then
    (mkCase (s! "fuzz/hit/pair/0/{tag}") (mkIntCaseStack (.cell uintRoot4Two) 0 4), rng2)
  else if shape = 3 then
    (mkCase (s! "fuzz/hit/pair/15/{tag}") (mkIntCaseStack (.cell uintRoot4Two) 15 4), rng2)
  else if shape = 4 then
    (mkCase (s! "fuzz/hit/n0/{tag}") (mkIntCaseStack (.cell uintRoot0) 0 0), rng2)
  else if shape = 5 then
    (mkCase (s! "fuzz/hit/n8/{tag}") (mkIntCaseStack (.cell uintRoot8Single) 0xA5 8), rng2)
  else if shape = 6 then
    (mkCase (s! "fuzz/miss/null/{tag}") (mkIntCaseStack .null 7 4), rng2)
  else if shape = 7 then
    (mkCase (s! "fuzz/miss/non-empty/{tag}") (mkIntCaseStack (.cell uintRoot4Two) 7 4), rng2)
  else if shape = 8 then
    (mkCase (s! "fuzz/miss/n0/{tag}") (mkIntCaseStack (.cell uintRoot8Single) 0xA5 9), rng2)
  else if shape = 9 then
    (mkCase (s! "fuzz/underflow/empty/{tag}") #[], rng2)
  else if shape = 10 then
    (mkCase (s! "fuzz/underflow/one/{tag}") #[.cell uintRoot4Single0], rng2)
  else if shape = 11 then
    (mkCase (s! "fuzz/underflow/two/{tag}") #[.cell uintRoot4Single0, intV 7], rng2)
  else if shape = 12 then
    (mkCase (s! "fuzz/range/n-neg/{tag}") (mkIntCaseStack (.cell uintRoot4Two) 0 (-1)), rng2)
  else if shape = 13 then
    (mkCase (s! "fuzz/range/n-hi/{tag}") (mkIntCaseStack (.cell uintRoot4Two) 0 1024), rng2)
  else if shape = 14 then
    (mkCase (s! "fuzz/range/key-high/{tag}") (mkIntCaseStack (.cell uintRoot4Two) 16 4), rng2)
  else if shape = 15 then
    (mkCase (s! "fuzz/range/key-low/{tag}") (mkIntCaseStack (.cell uintRoot4Two) (-1) 4), rng2)
  else if shape = 16 then
    (mkCase (s! "fuzz/type/n-non-int/{tag}") #[.cell uintRoot4Two, intV 4, .slice (mkSliceFromBits #[])], rng2)
  else if shape = 17 then
    (mkCase (s! "fuzz/type/dict-not-cell/{tag}") #[intV 4, intV 4, intV 4], rng2)
  else if shape = 18 then
    (mkCase (s! "fuzz/type/key-not-int/{tag}") #[.cell uintRoot4Two, .slice (Slice.ofCell sampleCellA), intV 4], rng2)
  else if shape = 19 then
    (mkCase (s! "fuzz/malformed-root/{tag}") (mkIntCaseStack (.cell malformedRoot) 0 4), rng2)
  else if shape = 20 then
    (mkCase (s! "fuzz/payload/bits/{tag}") (mkIntCaseStack (.cell uintRoot4BadBits) 9 4), rng2)
  else if shape = 21 then
    (mkCase (s! "fuzz/payload/no-ref/{tag}") (mkIntCaseStack (.cell uintRoot4BadNoRef) 3 4), rng2)
  else if shape = 22 then
    (mkCase (s! "fuzz/payload/two-refs/{tag}") (mkIntCaseStack (.cell uintRoot4BadTwoRefs) 11 4), rng2)
  else if shape = 23 then
    (mkCaseCode (s! "fuzz/decode/underbound/{tag}") #[] dictUdelGetNeighborLowerGap, rng2)
  else if shape = 24 then
    (mkCase (s! "fuzz/gas/exact/{tag}") (mkIntCaseStack .null 1 4) dictUdelGetGasExact, rng2)
  else
    (mkCase (s! "fuzz/gas/exact-minus-one/{tag}") (mkIntCaseStack .null 1 4) dictUdelGetGasExactMinusOne, rng2)

def suite : InstrSuite where
  id := dictUdelGetId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/fallback" (runDictUdelGetFallback #[]) #[intV dispatchSentinel]
    },
    { name := "unit/runtime/hit/single-0"
      run := do
        expectOkStack "runtime/hit/single-0"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Single0) 0 4))
          #[.null, .slice valueSliceA, intV (-1)]
    },
    { name := "unit/runtime/hit/single-15"
      run := do
        expectOkStack "runtime/hit/single-15"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Single15) 15 4))
          #[.null, .slice valueSliceB, intV (-1)]
    },
    { name := "unit/runtime/hit/pair-0"
      run := do
        expectOkStack "runtime/hit/pair-0"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Two) 0 4))
          #[.cell uintRoot4Single15, .slice valueSliceA, intV (-1)]
    },
    { name := "unit/runtime/hit/pair-15"
      run := do
        expectOkStack "runtime/hit/pair-15"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Two) 15 4))
          #[.cell uintRoot4Single0, .slice valueSliceB, intV (-1)]
    },
    { name := "unit/runtime/hit/payload/no-ref"
      run := do
        expectOkStack "runtime/hit/payload/no-ref"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4BadNoRef) 3 4))
          #[.null, .slice (mkSliceFromBits #[]), intV (-1)]
    },
    { name := "unit/runtime/hit/payload/two-refs"
      run := do
        expectOkStack "runtime/hit/payload/two-refs"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4BadTwoRefs) 11 4))
          #[.null, .slice valueSliceTwoRefs, intV (-1)]
    },
    { name := "unit/runtime/miss/null-root"
      run := do
        expectOkStack "runtime/miss/null-root"
          (runDictUdelGetDirect (mkIntCaseStack .null 7 4))
          #[.null, intV 0]
    },
    { name := "unit/runtime/miss/non-empty-root"
      run := do
        expectOkStack "runtime/miss/non-empty-root"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Two) 7 4))
          #[.cell uintRoot4Two, intV 0]
    },
    { name := "unit/runtime/miss/malformed-root"
      run := do
        expectErr "runtime/malformed-root" (runDictUdelGetDirect (mkIntCaseStack (.cell malformedRoot) 0 4))
          .cellUnd
    },
    { name := "unit/runtime/type/n-non-int"
      run := do
        expectErr "runtime/type-non-int"
          (runDictUdelGetDirect #[.cell uintRoot4Two, intV 4, .slice (Slice.ofCell sampleCellA)])
          .typeChk
    },
    { name := "unit/runtime/type/dict-not-cell"
      run := do
        expectErr "runtime/type-dict-not-cell"
          (runDictUdelGetDirect #[intV 4, intV 4, intV 4])
          .typeChk
    },
    { name := "unit/runtime/type/key-not-int"
      run := do
        expectErr "runtime/key-not-int"
          (runDictUdelGetDirect #[.cell uintRoot4Two, .slice (Slice.ofCell sampleCellA), intV 4])
          .typeChk
    },
    { name := "unit/runtime/range/n-negative"
      run := do
        expectErr "runtime/range-n-negative"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Two) 0 (-1)))
          .rangeChk
    },
    { name := "unit/runtime/range/n-too-large"
      run := do
        expectErr "runtime/range-n-too-large"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Two) 0 1024))
          .rangeChk
    },
    { name := "unit/runtime/range/key-nil"
      run := do
        expectErr "runtime/range-key-nil"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Two) 1 0))
          .rangeChk
    },
    { name := "unit/runtime/range/key-high"
      run := do
        expectErr "runtime/range-key-high"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Two) 16 4))
          .rangeChk
    },
    { name := "unit/runtime/range/key-low"
      run := do
        expectErr "runtime/range-key-low"
          (runDictUdelGetDirect (mkIntCaseStack (.cell uintRoot4Two) (-1) 4))
          .rangeChk
    },
    { name := "unit/runtime/range/key-nan"
      run := do
        expectErr "runtime/range-key-nan"
          (runDictUdelGetDirect #[.cell uintRoot4Two, .int .nan, intV 4])
          .rangeChk
    },
    { name := "unit/runtime/underflow/empty"
      run := do
        expectErr "runtime/underflow-empty" (runDictUdelGetDirect #[]) .stkUnd
    },
    { name := "unit/runtime/underflow/one-item"
      run := do
        expectErr "runtime/underflow-one-item" (runDictUdelGetDirect #[.cell uintRoot4Two]) .stkUnd
    },
    { name := "unit/runtime/underflow/two-items"
      run := do
        expectErr "runtime/underflow-two-items" (runDictUdelGetDirect #[.cell uintRoot4Two, intV 7]) .stkUnd
    },
    { name := "unit/decode/target"
      run := do
        expectDecodeOk "decode/target" dictUdelGetCode dictUdelGetInstr
    },
    { name := "unit/decode/neighbor/signed"
      run := do
        expectDecodeOk "decode/neighbor-signed" dictUdelGetNeighborSignedCode (.dictExt (.mutGet true false false .del))
    },
    { name := "unit/decode/neighbor/unsigned-ref"
      run := do
        expectDecodeOk "decode/neighbor-unsigned-ref" dictUdelGetNeighborUnsignedRefCode (.dictExt (.mutGet true true true .del))
    },
    { name := "unit/decode/lower-boundary"
      run := do
        expectDecodeErr "decode/lower-boundary" dictUdelGetNeighborLowerGap .invOpcode
    },
    { name := "unit/decode/upper-boundary"
      run := do
        expectDecodeErr "decode/upper-boundary" dictUdelGetNeighborUpperGap .invOpcode
    },
    { name := "unit/decode/truncated-8"
      run := do
        expectDecodeErr "decode/truncated-8" (Cell.mkOrdinary (natToBits 0xf4 8) #[]) .invOpcode
    },
    { name := "unit/decode/truncated-15"
      run := do
        expectDecodeErr "decode/truncated-15" (Cell.mkOrdinary (natToBits (0xf466 >>> 1) 15) #[]) .invOpcode
    },
    { name := "unit/assemble/unsupported"
      run := do
        expectAssembleErr "assemble/unsupported" dictUdelGetInstr .invOpcode
    }
  ]
  oracle := #[
    mkCase "oracle/hit/single-0" (mkIntCaseStack (.cell uintRoot4Single0) 0 4) -- [B6]
    , -- [B6][B7]
    mkCase "oracle/hit/single-15" (mkIntCaseStack (.cell uintRoot4Single15) 15 4) -- [B6][B7]
    , -- [B6][B7]
    mkCase "oracle/hit/pair-0" (mkIntCaseStack (.cell uintRoot4Two) 0 4) -- [B6][B7]
    , -- [B6]
    mkCase "oracle/hit/pair-15" (mkIntCaseStack (.cell uintRoot4Two) 15 4) -- [B6]
    , -- [B6]
    mkCase "oracle/hit/n0" (mkIntCaseStack (.cell uintRoot0) 0 0) -- [B6][B7]
    , -- [B6]
    mkCase "oracle/hit/n8" (mkIntCaseStack (.cell uintRoot8Single) 0xA5 8) -- [B6][B7]
    , -- [B6]
    mkCase "oracle/miss/null-root" (mkIntCaseStack .null 7 4) -- [B6]
    , -- [B6]
    mkCase "oracle/miss/non-empty-root" (mkIntCaseStack (.cell uintRoot4Two) 7 4) -- [B6]
    , -- [B6]
    mkCase "oracle/miss/zero-width" (mkIntCaseStack (.cell uintRoot8Single) 0xA5 9) -- [B6]
    , -- [B6]
    mkCase "oracle/miss/boundary-n1023" (mkIntCaseStack (.cell uintRoot0) 0 1023) -- [B6]
    , -- [B6]
    mkCase "oracle/payload/bits" (mkIntCaseStack (.cell uintRoot4BadBits) 9 4) -- [B7]
    , -- [B7]
    mkCase "oracle/payload/no-ref" (mkIntCaseStack (.cell uintRoot4BadNoRef) 3 4) -- [B7]
    , -- [B7]
    mkCase "oracle/payload/two-refs" (mkIntCaseStack (.cell uintRoot4BadTwoRefs) 11 4) -- [B7]
    , -- [B7]
    mkCase "oracle/underflow/empty" #[] -- [B2]
    , -- [B2]
    mkCase "oracle/underflow/one-item" #[.cell uintRoot4Two] -- [B2]
    , -- [B2]
    mkCase "oracle/underflow/two-items" #[.cell uintRoot4Two, intV 7] -- [B2]
    , -- [B2]
    mkCase "oracle/range/n-negative" (mkIntCaseStack (.cell uintRoot4Two) 0 (-1)) -- [B3][B4][B5]
    , -- [B3][B4][B5]
    mkCase "oracle/range/n-too-large" (mkIntCaseStack (.cell uintRoot4Two) 0 1024) -- [B3]
    , -- [B3]
    mkCase "oracle/range/n-zero" (mkIntCaseStack (.cell uintRoot4Two) 0 0) -- [B5]
    , -- [B5]
    mkCase "oracle/range/key-high" (mkIntCaseStack (.cell uintRoot4Two) 16 4) -- [B4][B5]
    , -- [B4][B5]
    mkCase "oracle/range/key-low" (mkIntCaseStack (.cell uintRoot4Two) (-1) 4) -- [B4][B5]
    , -- [B4][B5]
    mkCase "oracle/range/key-nan" #[.cell uintRoot4Two, .int .nan, intV 4] -- [B4][B5]
    , -- [B4][B5]
    mkCase "oracle/type/n-non-int" #[.cell uintRoot4Two, intV 0, .slice (Slice.ofCell sampleCellA)] -- [B3]
    , -- [B3]
    mkCase "oracle/type/dict-not-cell" #[.slice (mkSliceFromBits #[]), intV 4, intV 4] -- [B4]
    , -- [B4]
    mkCase "oracle/type/key-not-int" #[.cell uintRoot4Two, .cell sampleCellA, intV 4] -- [B4]
    , -- [B4]
    mkCase "oracle/malformed-root" (mkIntCaseStack (.cell malformedRoot) 0 4) -- [B8]
    , -- [B8]
    mkCaseCode "oracle/decode/target" #[] dictUdelGetCode -- [B10]
    , -- [B10]
    mkCaseCode "oracle/decode/neighbor-signed" #[] dictUdelGetNeighborSignedCode -- [B10]
    , -- [B10]
    mkCaseCode "oracle/decode/neighbor-unsigned-ref" #[] dictUdelGetNeighborUnsignedRefCode -- [B10]
    , -- [B10]
    mkCaseCode "oracle/decode/lower-boundary" #[] dictUdelGetNeighborLowerGap -- [B10]
    , -- [B10]
    mkCaseCode "oracle/decode/upper-boundary" #[] dictUdelGetNeighborUpperGap -- [B10]
    , -- [B10]
    mkCaseCode "oracle/decode/truncated-8" #[] (Cell.mkOrdinary (natToBits 0xf4 8) #[]) -- [B10]
    , -- [B10]
    mkCaseCode "oracle/decode/truncated-15" #[] (Cell.mkOrdinary (natToBits (0xf466 >>> 1) 15) #[]) -- [B10]
    , -- [B10]
    mkCase "oracle/gas/exact-miss" (mkIntCaseStack .null 7 4) dictUdelGetGasExact -- [B11]
    , -- [B11]
    mkCase "oracle/gas/exact-minus-one-miss" (mkIntCaseStack .null 7 4) dictUdelGetGasExactMinusOne -- [B11]
    , -- [B11]
    mkCase "oracle/gas/exact-hit-single" (mkIntCaseStack (.cell uintRoot4Single0) 0 4) dictUdelGetGasExact -- [B11]
    , -- [B11]
    mkCase "oracle/gas/exact-minus-one-hit-single" (mkIntCaseStack (.cell uintRoot4Single0) 0 4) dictUdelGetGasExactMinusOne -- [B11]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictUdelGetId
      count := 500
      gen := genDICTUDELGETFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUDELGET
