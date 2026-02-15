import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIDELGETREF

/-!
INSTRUCTION: DICTIDELGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path:
   - `.dictExt (.mutGet true false true .del)` executes in `execInstrDictExt`.
   - Any non-`dictExt` instruction falls through to `next`.

2. [B2] Runtime stack shape / underflow:
   - `checkUnderflow 3` enforces `(n, dict, key)` availability.
   - Any short stack triggers `.stkUnd` before type conversions.

3. [B3] Runtime validation:
   - `n` is parsed with `popNatUpTo 1023`:
     - non-int `n` -> `.typeChk` (via `popInt`);
     - `.nan`, negative, or `n > 1023` -> `.rangeChk`.
   - `dict` input uses `popMaybeCell`:
     - `.null` and `.cell` are accepted;
     - others -> `.typeChk`.
   - `key` is popped as int (since intKey=true):
     - non-int key -> `.typeChk`;
     - `.nan` key -> `.rangeChk`;
     - `dictKeyBits?` outside signed range for `(key, n)` -> `.rangeChk`.

4. [B4] Runtime success paths:
   - Lookup miss:
     - `dictDeleteWithCells` returns `none`;
     - pushes updated dict root and `.int 0`.
   - Lookup hit:
     - `dictDeleteWithCells` returns `some oldVal`;
     - byRef mode calls `extractRefOrThrow oldVal`;
     - pushes updated dict root, old value as `.cell`, then `.int (-1)`.
   - Both success paths can run on empty and non-empty roots.

5. [B5] byRef payload shape:
   - `extractRefOrThrow` requires extracted slice with `bits=0` and `refs=1`.
   - Any other payload shape (bits, wrong ref count) throws `.dictErr`.

6. [B6] Gas behavior:
   - Gas uses normal `execInstr` budget (`computeExactGasBudget`) plus dynamic `consumeCreatedGas`;
   - exact-budget and exact-budget-minus-one behavior can be asserted with oracle gas limits.

7. [B7] Assembler behavior:
   - `.dictExt` instructions are encodable by `assembleCp0`; decode roundtrip is required.

8. [B8] Decoder behavior:
   - `.dictExt (.mutGet true false true .del)` is decode target `0xf465`.
   - `0xf462..0xf467` is the whole `DICT*DELGET*` mutget range.
   - `0xf461` and `0xf468` are decode boundaries and must fail `.invOpcode`.
   - Neighbors (`0xf464`, `0xf467`) decode as other DELGET variants.

TOTAL BRANCHES: 8
-/

private def dictIdelGetRefId : InstrId := { name := "DICTIDELGETREF" }

private def dictIdelGetRefInstr : Instr := .dictExt (.mutGet true false true .del)

private def dictIdelGetRefCode : Cell := Cell.mkOrdinary (natToBits 0xf465 16) #[]

private def rawCell16 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 16) #[]

private def dispatchSentinel : Int := 64123

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

private def keyBitsFor (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bs => bs
  | none => panic! s!"invalid key encoding for idx={idx}, n={n}, unsigned={unsigned}"

private def mkDictRefRoot (key : BitString) (value : Cell) : Cell :=
  match dictSetRefWithCells none key value .set with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) => panic! "expected dict root to be created, got none"
  | .error e => panic! s!"dictSetRefWithCells failed: {reprStr e}"

private def mkDictRefRoot2 (k1 : BitString) (v1 : Cell) (k2 : BitString) (v2 : Cell) : Cell :=
  match dictSetRefWithCells none k1 v1 .set with
  | .ok (some root1, _, _, _) =>
      match dictSetRefWithCells (some root1) k2 v2 .set with
      | .ok (some root2, _, _, _) => root2
      | .ok (none, _, _, _) => panic! "expected nested dict set to create root"
      | .error e => panic! s!"dictSetRefWithCells failed (2/2): {reprStr e}"
  | .ok (none, _, _, _) => panic! "expected first-level dict set to create root"
  | .error e => panic! s!"dictSetRefWithCells failed (1/2): {reprStr e}"

private def mkDictSliceRoot (key : BitString) (value : Slice) : Cell :=
  match dictSetSliceWithCells none key value .set with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) => panic! "expected dict root to be created, got none"
  | .error e => panic! s!"dictSetSliceWithCells failed: {reprStr e}"

private def intSignedRoot4SingleNeg1 : Cell :=
  mkDictRefRoot (keyBitsFor (-1) 4 false) sampleCellA

private def intSignedRoot4Single2 : Cell :=
  mkDictRefRoot (keyBitsFor 2 4 false) sampleCellB

private def intSignedRoot4 : Cell :=
  mkDictRefRoot2 (keyBitsFor (-1) 4 false) sampleCellA (keyBitsFor 2 4 false) sampleCellB

private def intSignedBadBitsRoot4 : Cell :=
  mkDictSliceRoot (keyBitsFor 3 4 false) (Slice.ofCell valueCellWithBits)

private def intSignedBadNoRefRoot4 : Cell :=
  mkDictSliceRoot (keyBitsFor 1 4 false) (Slice.ofCell valueCellNoRef)

private def intSignedBadTwoRefsRoot4 : Cell :=
  mkDictSliceRoot (keyBitsFor 0 4 false) (Slice.ofCell valueCellTwoRefs)

private def mkIntCaseStack (root : Value) (key : Int) (n : Int) : Array Value :=
  #[root, intV key, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIdelGetRefId
    codeCell? := some dictIdelGetRefCode
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
    instr := dictIdelGetRefId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictIdelGetRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt dictIdelGetRefInstr
    (match stack with
     | #[dict, key, n] => #[key, dict, n]
     | _ => stack)

private def runDictIdelGetRefFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV dispatchSentinel)) stack

private def dictIdelGetRefGas : Int :=
  computeExactGasBudget dictIdelGetRefInstr

private def dictIdelGetRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictIdelGetRefGas

private def dictIdelGetRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictIdelGetRefGas

private def expectDecodeOk (label : String) (code : Cell) (expected : Instr) : IO Unit := do
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

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembly error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleOk (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assembly success, got error {e}")
  | .ok code =>
      expectDecodeOk label code instr

private def genDictIdelGetRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  if shape = 0 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/ok/hit/single-neg1/{tag}") (mkIntCaseStack (.cell intSignedRoot4SingleNeg1) (-1) 4), rng2)
  else if shape = 1 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/ok/hit/single-2/{tag}") (mkIntCaseStack (.cell intSignedRoot4Single2) 2 4), rng2)
  else if shape = 2 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/ok/hit/two-entry/{tag}") (mkIntCaseStack (.cell intSignedRoot4) (-1) 4), rng2)
  else if shape = 3 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/ok/miss/null-root/{tag}") (mkIntCaseStack .null 7 4), rng2)
  else if shape = 4 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/ok/miss/non-empty/{tag}") (mkIntCaseStack (.cell intSignedRoot4) 7 4), rng2)
  else if shape = 5 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/ok/underflow/empty/{tag}") #[], rng2)
  else if shape = 6 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/ok/underflow/two-items/{tag}") #[.cell intSignedRoot4, intV 7], rng2)
  else if shape = 7 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/type-non-int/{tag}") #[.cell intSignedRoot4, intV (-1), .slice (Slice.ofCell sampleCellA)], rng2)
  else if shape = 8 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/type-dict/{tag}") #[intV 4, intV 2, intV 4], rng2)
  else if shape = 9 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/type-key/{tag}") #[.cell intSignedRoot4, .cell sampleCellA, intV 4], rng2)
  else if shape = 10 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/range/n-neg/{tag}") #[.cell intSignedRoot4, intV 2, intV (-1)], rng2)
  else if shape = 11 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/range/n-too-large/{tag}") #[.cell intSignedRoot4, intV 2, intV 1024], rng2)
  else if shape = 12 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/range/key-high/{tag}") #[.cell intSignedRoot4, intV 8, intV 4], rng2)
  else if shape = 13 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/range/key-low/{tag}") #[.cell intSignedRoot4, intV (-9), intV 4], rng2)
  else if shape = 14 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/range/key-nan/{tag}") #[.cell intSignedRoot4, .int .nan, intV 4], rng2)
  else if shape = 15 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/err/dicterr/bits/{tag}") (mkIntCaseStack (.cell intSignedBadBitsRoot4) 3 4), rng2)
  else if shape = 16 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCaseCode (s!"fuzz/decode/below-boundary/{tag}") #[] (rawCell16 0xf461), rng2)
  else if shape = 17 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCaseCode (s!"fuzz/decode/above-boundary/{tag}") #[] (rawCell16 0xf468), rng2)
  else if shape = 18 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/gas/exact/{tag}") (mkIntCaseStack .null 7 4) dictIdelGetRefGasExact, rng2)
  else
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase (s!"fuzz/gas/exact-minus-one/{tag}") (mkIntCaseStack .null 7 4) dictIdelGetRefGasExactMinusOne, rng2)

def suite : InstrSuite where
  id := dictIdelGetRefId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/fallback" (runDictIdelGetRefFallback #[]) #[intV dispatchSentinel] },
    { name := "unit/runtime/hit/single-neg1"
      run := do
        expectOkStack "runtime/single-hit/single-neg1"
          (runDictIdelGetRefDirect (mkIntCaseStack (.cell intSignedRoot4SingleNeg1) (-1) 4))
          #[.null, .cell sampleCellA, intV (-1)] },
    { name := "unit/runtime/hit/single-2"
      run := do
        expectOkStack "runtime/single-hit/single-2"
          (runDictIdelGetRefDirect (mkIntCaseStack (.cell intSignedRoot4Single2) 2 4))
          #[.null, .cell sampleCellB, intV (-1)] },
    { name := "unit/runtime/hit/two-entry-root"
      run := do
        expectOkStack "runtime/hit/two-entry-root"
          (runDictIdelGetRefDirect (mkIntCaseStack (.cell intSignedRoot4) (-1) 4))
          #[.cell intSignedRoot4Single2, .cell sampleCellA, intV (-1)] },
    { name := "unit/runtime/miss/null-root"
      run := do
        expectOkStack "runtime/miss/null-root"
          (runDictIdelGetRefDirect (mkIntCaseStack .null 7 4))
          #[.null, intV 0] },
    { name := "unit/runtime/miss/non-empty-root"
      run := do
        expectOkStack "runtime/miss/non-empty-root"
          (runDictIdelGetRefDirect (mkIntCaseStack (.cell intSignedRoot4) 7 4))
          #[.cell intSignedRoot4, intV 0] },
    { name := "unit/runtime/underflow/empty"
      run := do
        expectErr "runtime/underflow-empty" (runDictIdelGetRefDirect #[]) .stkUnd },
    { name := "unit/runtime/underflow/two-items"
      run := do
        expectErr "runtime/underflow-two-items" (runDictIdelGetRefDirect #[.cell intSignedRoot4, intV 2]) .stkUnd },
    { name := "unit/runtime/type/n-non-int"
      run := do
        expectErr "runtime/type-non-int"
          (runDictIdelGetRefDirect #[.cell intSignedRoot4, intV (-1), .slice (Slice.ofCell sampleCellA)])
          .typeChk },
    { name := "unit/runtime/type/dict-not-cell"
      run := do
        expectErr "runtime/type-dict-not-cell" (runDictIdelGetRefDirect #[intV 4, intV 2, intV 4]) .typeChk },
    { name := "unit/runtime/type/key-not-int"
      run := do
        expectErr "runtime/type-key-not-int"
          (runDictIdelGetRefDirect #[.cell intSignedRoot4, .slice (Slice.ofCell sampleCellA), intV 4])
          .typeChk },
    { name := "unit/runtime/range/n-negative"
      run := do
        expectErr "runtime/range-n-negative" (runDictIdelGetRefDirect #[.cell intSignedRoot4, intV 2, intV (-1)]) .rangeChk },
    { name := "unit/runtime/range/n-too-large"
      run := do
        expectErr "runtime/range-n-too-large" (runDictIdelGetRefDirect #[.cell intSignedRoot4, intV 2, intV 1024]) .rangeChk },
    { name := "unit/runtime/range/key-high"
      run := do
        expectErr "runtime/range-key-high" (runDictIdelGetRefDirect #[.cell intSignedRoot4, intV 8, intV 4]) .rangeChk },
    { name := "unit/runtime/range/key-low"
      run := do
        expectErr "runtime/range-key-low" (runDictIdelGetRefDirect #[.cell intSignedRoot4, intV (-9), intV 4]) .rangeChk },
    { name := "unit/runtime/range/key-nan"
      run := do
        expectErr "runtime/range-key-nan" (runDictIdelGetRefDirect #[.cell intSignedRoot4, .int .nan, intV 4]) .rangeChk },
    { name := "unit/runtime/dicterr/payload-with-bits"
      run := do
        expectErr "runtime/dicterr/payload-with-bits"
          (runDictIdelGetRefDirect (mkIntCaseStack (.cell intSignedBadBitsRoot4) 3 4))
          .dictErr },
    { name := "unit/runtime/dicterr/payload-no-ref"
      run := do
        expectErr "runtime/dicterr/payload-no-ref"
          (runDictIdelGetRefDirect (mkIntCaseStack (.cell intSignedBadNoRefRoot4) 1 4))
          .dictErr },
    { name := "unit/runtime/dicterr/payload-two-refs"
      run := do
        expectErr "runtime/dicterr/payload-two-refs"
          (runDictIdelGetRefDirect (mkIntCaseStack (.cell intSignedBadTwoRefsRoot4) 0 4))
          .dictErr },
    { name := "unit/decode/target"
      run := do
        expectDecodeOk "decode/target" dictIdelGetRefCode dictIdelGetRefInstr },
    { name := "unit/decode/neighbor-signed"
      run := do
        expectDecodeOk "decode/neighbor-signed" (rawCell16 0xf464) (.dictExt (.mutGet true false false .del)) },
    { name := "unit/decode/neighbor-unsigned-ref"
      run := do
        expectDecodeOk "decode/neighbor-unsigned-ref" (rawCell16 0xf467) (.dictExt (.mutGet true true true .del)) },
    { name := "unit/decode/underbound"
      run := do
        expectDecodeErr "decode/underbound" (rawCell16 0xf461) .invOpcode },
    { name := "unit/decode/overbound"
      run := do
        expectDecodeErr "decode/overbound" (rawCell16 0xf468) .invOpcode },
    { name := "unit/decode/truncated-8"
      run := do
        expectDecodeErr "decode/truncated-8" (Cell.mkOrdinary (natToBits 0xf4 8) #[]) .invOpcode },
    { name := "unit/decode/truncated-15"
      run := do
        expectDecodeErr "decode/truncated-15" (Cell.mkOrdinary (natToBits (0xf465 >>> 1) 15) #[]) .invOpcode },
    { name := "unit/assemble/encodes"
      run := do
        expectAssembleOk "assemble/encodes" dictIdelGetRefInstr }
  ]
  oracle := #[
    -- [B4] Found in single-entry root.
    mkCase "ok/hit/single-neg1" (mkIntCaseStack (.cell intSignedRoot4SingleNeg1) (-1) 4)
    -- [B4] Found in single-entry root with different key.
    , mkCase "ok/hit/single-2" (mkIntCaseStack (.cell intSignedRoot4Single2) 2 4)
    -- [B4] Found in two-entry root.
    , mkCase "ok/hit/two-entry" (mkIntCaseStack (.cell intSignedRoot4) (-1) 4)
    -- [B4] Missing in empty root.
    , mkCase "ok/miss/empty" (mkIntCaseStack .null 7 4)
    -- [B4] Missing in non-empty root.
    , mkCase "ok/miss/non-empty" (mkIntCaseStack (.cell intSignedRoot4) 7 4)
    , mkCase "ok/miss/zero-width" (mkIntCaseStack .null 0 0)
    -- [B4] Miss with key outside active leaf path.
    , mkCase "ok/miss/non-match-2" (mkIntCaseStack (.cell intSignedRoot4) 0 4)
    -- [B2] Empty stack underflow.
    , mkCase "err/underflow/empty" #[]
    -- [B2] Two-item underflow.
    , mkCase "err/underflow/two-items" #[.cell intSignedRoot4, intV 2]
    -- [B2] One-item underflow for key.
    , mkCase "err/underflow/one-item" #[.cell intSignedRoot4, intV 3]
    -- [B3] n type error.
    , mkCase "err/type/n-not-int" #[.cell intSignedRoot4, intV (-1), .slice (Slice.ofCell sampleCellA)]
    -- [B3] dict root type error.
    , mkCase "err/type/dict-not-cell" #[intV 4, intV 2, intV 4]
    -- [B3] key type error.
    , mkCase "err/type/key-not-int" #[.cell intSignedRoot4, .cell sampleCellA, intV 4]
    -- [B3] n negative range check.
    , mkCase "err/range/n-negative" #[.cell intSignedRoot4, intV 2, intV (-1)]
    -- [B3] n out-of-range high.
    , mkCase "err/range/n-too-large" #[.cell intSignedRoot4, intV 2, intV 1024]
    -- [B3] int key out-of-range high.
    , mkCase "err/range/key-high" #[.cell intSignedRoot4, intV 8, intV 4]
    -- [B3] int key out-of-range low.
    , mkCase "err/range/key-low" #[.cell intSignedRoot4, intV (-9), intV 4]
    -- [B3] int key NaN.
    , mkCase "err/range/key-nan" #[.cell intSignedRoot4, .int .nan, intV 4]
    -- [B5] Ref payload with non-zero bits.
    , mkCase "err/dicterr/payload-bits" (mkIntCaseStack (.cell intSignedBadBitsRoot4) 3 4)
    -- [B5] Ref payload with no refs.
    , mkCase "err/dicterr/payload-no-ref" (mkIntCaseStack (.cell intSignedBadNoRefRoot4) 1 4)
    -- [B5] Ref payload with too many refs.
    , mkCase "err/dicterr/payload-two-refs" (mkIntCaseStack (.cell intSignedBadTwoRefsRoot4) 0 4)
    -- [B7] Decode target opcode.
    , mkCaseCode "ok/decode/target" #[] dictIdelGetRefCode
    -- [B7] Decode signed neighbor opcode (x=0xf464) to non-byRef int variant.
    , mkCaseCode "ok/decode/neighbor-signed" #[] (rawCell16 0xf464)
    -- [B7] Decode unsigned-ref neighbor opcode (x=0xf467).
    , mkCaseCode "ok/decode/neighbor-unsigned-ref" #[] (rawCell16 0xf467)
    -- [B7] Decode lower boundary failure.
    , mkCaseCode "err/decode/below" #[] (rawCell16 0xf461)
    -- [B7] Decode upper boundary failure.
    , mkCaseCode "err/decode/above" #[] (rawCell16 0xf468)
    -- [B7] Decode/truncated failure path.
    , mkCaseCode "err/decode/truncated-8" #[] (Cell.mkOrdinary (natToBits 0xf4 8) #[])
    -- [B7] Decode/truncated failure path.
    , mkCaseCode "err/decode/truncated-15" #[] (Cell.mkOrdinary (natToBits (0xf465 >>> 1) 15) #[])
    -- [B8] Gas exact success with miss path.
    , mkCase "gas/exact/miss" (mkIntCaseStack .null 7 4) dictIdelGetRefGasExact
    -- [B8] Gas exact-minus-one failure with miss path.
    , mkCase "gas/exact-minus-one/miss" (mkIntCaseStack .null 7 4) dictIdelGetRefGasExactMinusOne
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genDictIdelGetRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIDELGETREF
