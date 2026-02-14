import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUDELGETREF

/-!
INSTRUCTION: DICTUDELGETREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch/runtime dispatch branch:
   - `execInstrDictExt` handles `.dictExt (.mutGet true true true .del)` only via the `mutGet` branch.
   - Any other instruction must follow `next` without stack effects.

2. [B2] Runtime stack-shape/underflow:
   - `VM.checkUnderflow 3` is required for `(n, dict, key)`.
   - Fewer than 3 values raises `.stkUnd`.
   - This is checked before any parsing or dictionary traversal.

3. [B3] Runtime parse + range validation path:
   - `n := popNatUpTo 1023`:
     - valid range: `0..1023`
     - `.rangeChk` for `n<0`, `.nan`, or `n>1023`.
   - `dict := popMaybeCell`: accepts `.null` and `.cell`; other types throw `.typeChk`.
   - integer `key` is parsed with `popInt`; non-int throws `.typeChk`.
   - `dictKeyBits? idx n true` handles unsigned range checks; invalid key yields `.rangeChk`.

4. [B4] Key-mapping and delete success/miss behavior:
   - On key conversion success, the branch executes `dictDeleteWithCells`.
   - If key is missing, the dictionary root is preserved (or empty `null`) and the flag `0` is pushed.
   - On hit, updated root is pushed and the extracted value is carried forward for by-ref extraction.

5. [B5] byRef extraction branch:
   - For `.dictExt` unsigned/int by-ref mode, `extractRefOrThrow` is applied to old value.
   - Requires value slice with `bitsRemaining == 0` and `refsRemaining == 1`; otherwise `.dictErr`.

6. [B6] Corrupted dictionary shape:
   - Malformed root structures can fail in traversal and raise `.dictErr`/`.cellUnd` before extraction.

7. [B7] Assembler branch:
   - `TvmLean/Model/Instr/Asm/Cp0.lean` does not encode `.dictExt`; assembly returns `.invOpcode`.

8. [B8] Decoder branch:
   - `0xf467` decodes to `.dictExt (.mutGet true true true .del)` (opcode family `0xf462..0xf467`).
   - `0xf466` and `0xf465` decode to neighboring DELGET forms.
   - `0xf461` and `0xf468` fail decode as `.invOpcode`.
   - Truncated inputs (for example 8- and 15-bit cells) also fail decode.

9. [B9] Gas accounting:
   - Base gas is fixed to `instrGas (.dictExt (.mutGet true true true .del)) 16`.
   - Exact and exact-minus-one branches are explicit.
   - Dictionary mutations may add dynamic gas via created cells and may not be constant across all cases.

TOTAL BRANCHES: 9
Every oracle test below is tagged with the branch(es) it covers.
-/

private def dictUDelGetRefId : InstrId :=
  { name := "DICTUDELGETREF" }

private def dictUDelGetRefInstr : Instr :=
  .dictExt (.mutGet true true true .del)

private def dictUDelGetRefCode : Cell :=
  Cell.mkOrdinary (natToBits 0xf467 16) #[]

private def rawCell16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def dispatchSentinel : Int := 4242

private def sampleCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def sampleCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x3b 8) #[]

private def sampleCellC : Cell :=
  Cell.mkOrdinary (natToBits 0x7f 8) #[]

private def valueCellWithBits : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def valueCellNoRef : Cell :=
  Cell.mkOrdinary #[] #[]

private def valueCellTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[sampleCellA, sampleCellB]

private def valueCellEmpty : Cell :=
  Cell.mkOrdinary #[] #[]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def dictUDelGetRefKeyBitsFor (idx : Int) (n : Nat) : BitString :=
  match dictKeyBits? idx n true with
  | some bs => bs
  | none => panic! s!"invalid unsigned dict key idx={idx}, n={n}"

private def mkIntCaseStack (root : Value) (key : Int) (n : Int) : Array Value :=
  #[root, intV key, intV n]

private def mkDictRefRoot (key : BitString) (value : Cell) : Cell :=
  match dictSetRefWithCells none key value .set with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) =>
      panic! "expected dict creation to succeed, got none"
  | .error e =>
      panic! s!"dictSetRefWithCells failed: {reprStr e}"

private def mkDictRefRoot2 (k1 : BitString) (v1 : Cell) (k2 : BitString) (v2 : Cell) : Cell :=
  match dictSetRefWithCells none k1 v1 .set with
  | .ok (some root1, _, _, _) =>
      match dictSetRefWithCells (some root1) k2 v2 .set with
      | .ok (some root2, _, _, _) => root2
      | .ok (none, _, _, _) => panic! "expected second insertion to produce dict root"
      | .error e => panic! s!"dictSetRefWithCells failed (2/2): {reprStr e}"
  | .ok (none, _, _, _) => panic! "expected first insertion to produce dict root"
  | .error e => panic! s!"dictSetRefWithCells failed (1/2): {reprStr e}"

private def mkDictSliceRoot (key : BitString) (value : Slice) : Cell :=
  match dictSetSliceWithCells none key value .set with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) =>
      panic! "expected dict creation to succeed, got none"
  | .error e =>
      panic! s!"dictSetSliceWithCells failed: {reprStr e}"

private def key4 (v : Nat) : BitString :=
  natToBits v 4

private def key8 (v : Nat) : BitString :=
  natToBits v 8

private def dictUDelGetRefRoot4Single5 : Cell :=
  mkDictRefRoot (dictUDelGetRefKeyBitsFor 5 4) sampleCellA

private def dictUDelGetRefRoot4Single7 : Cell :=
  mkDictRefRoot (dictUDelGetRefKeyBitsFor 7 4) sampleCellB

private def dictUDelGetRefRoot4Multi : Cell :=
  mkDictRefRoot2
    (dictUDelGetRefKeyBitsFor 5 4) sampleCellA
    (dictUDelGetRefKeyBitsFor 11 4) sampleCellB

private def dictUDelGetRefRoot4Zero : Cell :=
  mkDictRefRoot (dictUDelGetRefKeyBitsFor 0 0) sampleCellC

private def dictUDelGetRefRoot8Single : Cell :=
  mkDictRefRoot (dictUDelGetRefKeyBitsFor 200 8) sampleCellA

private def dictUDelGetRefRoot4BitsPayload : Cell :=
  mkDictSliceRoot (dictUDelGetRefKeyBitsFor 5 4) (Slice.ofCell valueCellWithBits)

private def dictUDelGetRefRoot4NoRefPayload : Cell :=
  mkDictSliceRoot (dictUDelGetRefKeyBitsFor 7 4) (Slice.ofCell valueCellEmpty)

private def dictUDelGetRefRoot4TwoRefsPayload : Cell :=
  mkDictSliceRoot (dictUDelGetRefKeyBitsFor 11 4) (Slice.ofCell valueCellTwoRefs)

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := dictUDelGetRefCode)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUDelGetRefId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictUDelGetRefFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.tonEnvOp .setGasLimit) (VM.push (intV dispatchSentinel)) stack

private def runDictUDelGetRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt dictUDelGetRefInstr stack

private def dictUDelGetRefGas : Int :=
  instrGas dictUDelGetRefInstr 16

private def dictUDelGetRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictUDelGetRefGas

private def dictUDelGetRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictUDelGetRefGas

private def expectDecodeOk (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected || bits != 16 || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: unexpected decode result {reprStr instr}")

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembly error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def genDICTUDELGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  if shape = 0 then
    (mkCase "fuzz/hit/single-5" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 4), rng1)
  else if shape = 1 then
    (mkCase "fuzz/hit/single-7" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single7) 7 4), rng1)
  else if shape = 2 then
    (mkCase "fuzz/hit/multi-5" (mkIntCaseStack (.cell dictUDelGetRefRoot4Multi) 5 4), rng1)
  else if shape = 3 then
    (mkCase "fuzz/hit/multi-11" (mkIntCaseStack (.cell dictUDelGetRefRoot4Multi) 11 4), rng1)
  else if shape = 4 then
    (mkCase "fuzz/hit/zero" (mkIntCaseStack (.cell dictUDelGetRefRoot4Zero) 0 0), rng1)
  else if shape = 5 then
    (mkCase "fuzz/hit/n8" (mkIntCaseStack (.cell dictUDelGetRefRoot8Single) 200 8), rng1)
  else if shape = 6 then
    (mkCase "fuzz/miss/null-4" (mkIntCaseStack .null 3 4), rng1)
  else if shape = 7 then
    (mkCase "fuzz/miss/non-empty" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 8 4), rng1)
  else if shape = 8 then
    (mkCase "fuzz/miss/null-0" (mkIntCaseStack .null 0 0), rng1)
  else if shape = 9 then
    (mkCase "fuzz/miss/null-boundary-1023" (mkIntCaseStack .null 0 1023), rng1)
  else if shape = 10 then
    (mkCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 11 then
    (mkCase "fuzz/underflow/two-items" #[.cell dictUDelGetRefRoot4Single5, intV 4], rng1)
  else if shape = 12 then
    (mkCase "fuzz/underflow/one-item" #[.cell dictUDelGetRefRoot4Single5], rng1)
  else if shape = 13 then
    (mkCase "fuzz/type/n-not-int" #[.cell dictUDelGetRefRoot4Single5, intV 5, .slice (Slice.ofCell valueCellEmpty)], rng1)
  else if shape = 14 then
    (mkCase "fuzz/type/dict-not-cell" #[intV 4, intV 5, intV 4], rng1)
  else if shape = 15 then
    (mkCase "fuzz/type/key-not-int" #[.cell dictUDelGetRefRoot4Single5, .slice (Slice.ofCell sampleCellA), intV 4], rng1)
  else if shape = 16 then
    (mkCase "fuzz/range/n-negative" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 (-1)), rng1)
  else if shape = 17 then
    (mkCase "fuzz/range/n-too-large" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 1024), rng1)
  else if shape = 18 then
    (mkCase "fuzz/range/key-negative" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) (-1) 4), rng1)
  else if shape = 19 then
    (mkCase "fuzz/range/key-too-large" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 16 4), rng1)
  else if shape = 20 then
    (mkCase "fuzz/range/key-nan" #[.cell dictUDelGetRefRoot4Single5, .int .nan, intV 4], rng1)
  else if shape = 21 then
    (mkCase "fuzz/dict-err/payload-bits" (mkIntCaseStack (.cell dictUDelGetRefRoot4BitsPayload) 5 4), rng1)
  else if shape = 22 then
    (mkCase "fuzz/dict-err/payload-no-ref" (mkIntCaseStack (.cell dictUDelGetRefRoot4NoRefPayload) 7 4), rng1)
  else if shape = 23 then
    (mkCase "fuzz/dict-err/payload-two-refs" (mkIntCaseStack (.cell dictUDelGetRefRoot4TwoRefsPayload) 11 4), rng1)
  else if shape = 24 then
    (mkCase "fuzz/decode/below" #[] (rawCell16 0xf461), rng1)
  else if shape = 25 then
    (mkCase "fuzz/decode/above" #[] (rawCell16 0xf468), rng1)
  else
    (mkCase "fuzz/decode/truncated-8" #[] (Cell.mkOrdinary (natToBits 0xf4 8) #[]), rng1)

def suite : InstrSuite where
  id := dictUDelGetRefId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "unit/dispatch/fallback"
          (runDictUDelGetRefFallback #[])
          #[intV dispatchSentinel]
    },
    { name := "unit/runtime/hit/single-5"
      run := do
        expectOkStack "unit/runtime/hit/single-5"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 4))
          #[.null, .cell sampleCellA, intV (-1)]
    },
    { name := "unit/runtime/miss/null-root"
      run := do
        expectOkStack "unit/runtime/miss/null-root"
          (runDictUDelGetRefDirect (mkIntCaseStack .null 3 4))
          #[.null, intV 0]
    },
    { name := "unit/runtime/miss/non-empty-root"
      run := do
        expectOkStack "unit/runtime/miss/non-empty-root"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 3 4))
          #[.cell dictUDelGetRefRoot4Single5, intV 0]
    },
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "unit/runtime/underflow-empty" (runDictUDelGetRefDirect #[]) .stkUnd
    },
    { name := "unit/runtime/underflow-two-items"
      run := do
        expectErr "unit/runtime/underflow-two-items" (runDictUDelGetRefDirect #[.cell dictUDelGetRefRoot4Single5, intV 5]) .stkUnd
    },
    { name := "unit/runtime/type-n-not-int"
      run := do
        expectErr "unit/runtime/type-n-not-int" (runDictUDelGetRefDirect #[.cell dictUDelGetRefRoot4Single5, intV 5, .slice (Slice.ofCell sampleCellA)]) .typeChk
    },
    { name := "unit/runtime/type-dict-not-cell"
      run := do
        expectErr "unit/runtime/type-dict-not-cell" (runDictUDelGetRefDirect #[intV 4, intV 5, intV 4]) .typeChk
    },
    { name := "unit/runtime/type-key-not-int"
      run := do
        expectErr "unit/runtime/type-key-not-int" (runDictUDelGetRefDirect #[.cell dictUDelGetRefRoot4Single5, .cell sampleCellA, intV 4]) .typeChk
    },
    { name := "unit/runtime/range/n-negative"
      run := do
        expectErr "unit/runtime/range-n-negative"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 (-1))) .rangeChk
    },
    { name := "unit/runtime/range/n-too-large"
      run := do
        expectErr "unit/runtime/range-n-too-large"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 1024)) .rangeChk
    },
    { name := "unit/runtime/range/key-negative"
      run := do
        expectErr "unit/runtime/range-key-negative"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) (-1) 4)) .rangeChk
    },
    { name := "unit/runtime/range/key-too-large"
      run := do
        expectErr "unit/runtime/range-key-too-large"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 16 4)) .rangeChk
    },
    { name := "unit/runtime/range/key-nan"
      run := do
        expectErr "unit/runtime/range-key-nan"
          (runDictUDelGetRefDirect #[.cell dictUDelGetRefRoot4Single5, .int .nan, intV 4]) .rangeChk
    },
    { name := "unit/runtime/dict-err/payload-bits"
      run := do
        expectErr "unit/runtime/dict-err/payload-bits"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4BitsPayload) 5 4)) .dictErr
    },
    { name := "unit/runtime/dict-err/payload-no-ref"
      run := do
        expectErr "unit/runtime/dict-err/payload-no-ref"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4NoRefPayload) 7 4)) .dictErr
    },
    { name := "unit/runtime/dict-err/payload-two-refs"
      run := do
        expectErr "unit/runtime/dict-err/payload-two-refs"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell dictUDelGetRefRoot4TwoRefsPayload) 11 4)) .dictErr
    },
    { name := "unit/runtime/dict-err/malformed-root"
      run := do
        expectErr "unit/runtime/dict-err/malformed-root"
          (runDictUDelGetRefDirect (mkIntCaseStack (.cell malformedDict) 5 4)) .dictErr
    },
    { name := "unit/decode/target"
      run := do
        expectDecodeOk "decode/target" dictUDelGetRefCode dictUDelGetRefInstr
    },
    { name := "unit/decode/neighbor-unsigned"
      run := do
        expectDecodeOk "decode/neighbor-unsigned"
          (rawCell16 0xf466) (.dictExt (.mutGet true true false .del))
    },
    { name := "unit/decode/neighbor-ref"
      run := do
        expectDecodeOk "decode/neighbor-ref" (rawCell16 0xf465)
          (.dictExt (.mutGet true false true .del))
    },
    { name := "unit/decode/below-bound"
      run := do
        expectDecodeErr "decode/below-bound" (rawCell16 0xf461) .invOpcode
    },
    { name := "unit/decode/above-bound"
      run := do
        expectDecodeErr "decode/above-bound" (rawCell16 0xf468) .invOpcode
    },
    { name := "unit/decode/truncated-8"
      run := do
        expectDecodeErr "decode/truncated-8" (Cell.mkOrdinary (natToBits 0xf4 8) #[]) .invOpcode
    },
    { name := "unit/decode/truncated-15"
      run := do
        expectDecodeErr "decode/truncated-15" (Cell.mkOrdinary (natToBits (0xf467 >>> 1) 15) #[]) .invOpcode
    },
    { name := "unit/assemble/unsupported"
      run := do
        expectAssembleErr "assemble/unsupported" dictUDelGetRefInstr .invOpcode
    }
  ]
  oracle := #[
    -- [B2] empty stack underflow (no-op branch not executing).
    mkCase "oracle/underflow-empty" #[], -- [B2]
    -- [B2] two-item underflow.
    mkCase "oracle/underflow-two-items" #[.cell dictUDelGetRefRoot4Single5, intV 5], -- [B2]
    -- [B2] one-item underflow.
    mkCase "oracle/underflow-one-item" #[.cell dictUDelGetRefRoot4Single5], -- [B2]
    -- [B3] malformed `n`: non-int for `n`.
    mkCase "oracle/type/n-not-int" #[.cell dictUDelGetRefRoot4Single5, intV 5, .slice (Slice.ofCell sampleCellA)], -- [B3]
    -- [B3] malformed dict operand.
    mkCase "oracle/type/dict-not-cell" #[intV 4, intV 5, intV 4], -- [B3]
    -- [B3] malformed key operand.
    mkCase "oracle/type/key-not-int" #[.cell dictUDelGetRefRoot4Single5, .slice (Slice.ofCell sampleCellA), intV 4], -- [B3]
    -- [B3] `n` out of range negative.
    mkCase "oracle/range/n-negative" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 (-1)), -- [B3]
    -- [B3] `n` out of range above limit.
    mkCase "oracle/range/n-too-large" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 1024), -- [B3]
    -- [B3] unsigned key below 0.
    mkCase "oracle/range/key-negative" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) (-1) 4), -- [B3]
    -- [B3] unsigned key above max for n=4.
    mkCase "oracle/range/key-too-large" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 16 4), -- [B3]
    -- [B4] single-key hit, unsigned 4-bit key.
    mkCase "oracle/hit/single-5" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 4), -- [B4][B5]
    -- [B4] single-key hit, boundary n=0.
    mkCase "oracle/hit/zero-key" (mkIntCaseStack (.cell dictUDelGetRefRoot4Zero) 0 0), -- [B4][B5]
    -- [B4] single-key hit with 8-bit key.
    mkCase "oracle/hit/eight-bit" (mkIntCaseStack (.cell dictUDelGetRefRoot8Single) 200 8), -- [B4][B5]
    -- [B4] multi-key hit first branch.
    mkCase "oracle/hit/multi-5" (mkIntCaseStack (.cell dictUDelGetRefRoot4Multi) 5 4), -- [B4][B5]
    -- [B4] multi-key hit second branch.
    mkCase "oracle/hit/multi-11" (mkIntCaseStack (.cell dictUDelGetRefRoot4Multi) 11 4), -- [B4][B5]
    -- [B4] miss path with empty dictionary.
    mkCase "oracle/miss/null-4" (mkIntCaseStack .null 3 4), -- [B4]
    -- [B4] miss path with non-empty dictionary.
    mkCase "oracle/miss/non-empty" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 8 4), -- [B4]
    -- [B4] miss path with n=0 and empty dictionary.
    mkCase "oracle/miss/null-0" (mkIntCaseStack .null 0 0), -- [B4]
    -- [B4] miss path with large n boundary.
    mkCase "oracle/miss/null-boundary-1023" (mkIntCaseStack .null 0 1023), -- [B4]
    -- [B5] by-ref payload with bits in old value.
    mkCase "oracle/payload/bits" (mkIntCaseStack (.cell dictUDelGetRefRoot4BitsPayload) 5 4), -- [B5][B6]
    -- [B5] by-ref payload with no refs.
    mkCase "oracle/payload/no-ref" (mkIntCaseStack (.cell dictUDelGetRefRoot4NoRefPayload) 7 4), -- [B5][B6]
    -- [B5] by-ref payload with multiple refs.
    mkCase "oracle/payload/two-refs" (mkIntCaseStack (.cell dictUDelGetRefRoot4TwoRefsPayload) 11 4), -- [B5][B6]
    -- [B6] malformed dict payload root.
    mkCase "oracle/dict-err/malformed-root" (mkIntCaseStack (.cell malformedDict) 5 4), -- [B6]
    -- [B7] decode boundary lower neighbor.
    mkCase "oracle/decode/target" #[] dictUDelGetRefCode, -- [B7][B8]
    -- [B7] decode lower boundary fail.
    mkCase "oracle/decode/below" #[] (rawCell16 0xf461), -- [B7][B8]
    -- [B7] decode upper boundary fail.
    mkCase "oracle/decode/above" #[] (rawCell16 0xf468), -- [B7][B8]
    -- [B7] decode truncated-8 fail.
    mkCase "oracle/decode/truncated-8" #[] (Cell.mkOrdinary (natToBits 0xf4 8) #[]), -- [B7][B8]
    -- [B7] decode truncated-15 fail.
    mkCase "oracle/decode/truncated-15" #[] (Cell.mkOrdinary (natToBits (0xf467 >>> 1) 15) #[]), -- [B7][B8]
    -- [B7] decode alias to DICTUDELGET.
    mkCase "oracle/decode/neighbor-unsigned" #[] (rawCell16 0xf466), -- [B7][B8]
    -- [B7] decode alias to DICTIDELGETREF.
    mkCase "oracle/decode/neighbor-ref" #[] (rawCell16 0xf465), -- [B7][B8]
    -- [B9] assembler-reject path.
    mkCase "oracle/asm/unsupported" #[] (rawCell16 0xf467), -- [B9] (via harness)
    -- [B9] exact gas miss-path.
    mkCase "oracle/gas/exact-miss" (mkIntCaseStack .null 3 4) (gasLimits := dictUDelGetRefGasExact), -- [B9]
    -- [B9] exact gas minus one miss-path.
    mkCase "oracle/gas/exact-minus-one-miss" (mkIntCaseStack .null 3 4) (gasLimits := dictUDelGetRefGasExactMinusOne), -- [B9]
    -- [B4] hit path with gas limit; exercises dynamic created-cell branch if any.
    mkCase "oracle/gas/exact-hit" (mkIntCaseStack (.cell dictUDelGetRefRoot4Single5) 5 4) (gasLimits := dictUDelGetRefGasExact), -- [B9][B4][B5]
    -- [B1] fallback neighbor decode (non-target) remains valid in same family.
    mkCase "oracle/decode/neighbor-signed" #[] (rawCell16 0xf464), -- [B1][B7][B8]
    -- [B3] key NaN path.
    mkCase "oracle/key-nan" #[.cell dictUDelGetRefRoot4Single5, .int .nan, intV 4] -- [B3]
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr dictUDelGetRefId
      count := 500
      gen := genDICTUDELGETREFFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUDELGETREF
