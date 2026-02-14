import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIDELGET

/-!
INSTRUCTION: DICTIDELGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch/runtime selection:
  - `execInstrDictExt` matches only `.dictExt`.
  - `.dictExt (.mutGet true false false .del)` must execute in this handler.
  - Any non-`dictExt` instruction must follow `next` without stack effects.

2. [B2] Runtime stack-shape validation:
  - `VM.checkUnderflow 3` rejects stacks with < 3 items.
  - A valid stack shape is `(n, dict, key)` with key as signed integer.
  - Underflow paths are exercised before key parsing and dictionary traversal.

3. [B3] Integer key/value parsing:
  - `n` is validated by `popNatUpTo 1023`.
  - `n < 0`, `.nan`, and `n > 1023` are `.rangeChk`.
  - Integer key is parsed with `popInt`; non-int errors become `.typeChk`.
  - `dictKeyBits?` returning `none` for `(key, n)` currently yields `.rangeChk` in Lean.

4. [B4] Signed integer key extraction boundary:
  - In C++ `exec_dict_deleteget`, out-of-range signed integer key is a miss result (`0`)
    with unchanged dictionary.
  - Lean currently throws `.rangeChk` because `dictKeyBits?` returns `none`.
  - This is a semantic mismatch to track with direct checks and oracle coverage.

5. [B5] Delete semantics:
  - `dictDeleteWithCells` miss path returns same root and `0`.
  - Hit path returns new root, old value slice as returned, and `-1`.
  - Deleted root shape after hit can shrink a dictionary and this branch is exercised in
    known single-root cases.

6. [B6] Dictionary root corruption:
  - Invalid dictionary roots cause traversal errors from delete path (`dictErr`/`cellUnd`
    depending on encoded shape).
  - Those errors happen before any value extraction.

7. [B7] Assembler path:
  - `.dictExt` cannot be assembled via `assembleCp0`; `.invOpcode` expected.

8. [B8] Decoder path:
  - Signed non-ref form maps to `0xf464`.
  - Decoder range is `0xf462..0xf467`; neighbors decode to `DICTDELGET`,
    `DICTIDELGETREF`, and `DICTUDELGET*` forms.
  - `0xf461` and `0xf468` must not decode and return `.invOpcode`.
  - Short/truncated inputs must fail decode.

9. [B9] Gas branches:
  - Base cost from single-instruction budget applies.
  - Exact-budget (`exact`) and exact-minus-one (`exactMinusOne`) behavior are required.

TOTAL BRANCHES: 9
Every oracle test below is tagged with the branch(es) it covers.
-/

private def dictIdelGetId : InstrId :=
  { name := "DICTIDELGET" }

private def dictIdelGetInstr : Instr :=
  .dictExt (.mutGet true false false .del)

private def dictIdelGetCode : Cell :=
  Cell.mkOrdinary (natToBits 0xf464 16) #[]

private def rawCell16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def dictIDelGetNeighborSliceCode : Cell :=
  rawCell16 0xf463

private def dictIDelGetNeighborByRefCode : Cell :=
  rawCell16 0xf465

private def dictIDelGetNeighborUnsignedCode : Cell :=
  rawCell16 0xf466

private def dictIDelGetNeighborUnsignedRefCode : Cell :=
  rawCell16 0xf467

private def dispatchSentinel : Int := 64123

private def sampleCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def sampleCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x3b 8) #[]

private def sampleCellC : Cell :=
  Cell.mkOrdinary (natToBits 0x17 8) #[]

private def valueCellWithBits : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def valueCellTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[sampleCellA, sampleCellB]

private def valueSliceA : Slice :=
  mkSliceFromBits (natToBits 0x5 4)

private def valueSliceB : Slice :=
  mkSliceFromBits (natToBits 0xA 4)

private def valueSliceC : Slice :=
  mkSliceFromBits (natToBits 0x1 4)

private def valueSliceBits : Slice :=
  Slice.ofCell valueCellWithBits

private def valueSliceTwoRefs : Slice :=
  Slice.ofCell valueCellTwoRefs

private def malformedRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def keyBitsFor (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bs => bs
  | none =>
      panic! s!"expected key bits for idx={idx}, n={n}, unsigned={unsigned}"

private def mkDictSliceRoot (key : BitString) (value : Slice) : Cell :=
  match dictSetSliceWithCells none key value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _ok, _created, _loaded) =>
      panic! "failed to build dict root: insertion returned none"
  | .error e =>
      panic! s!"dictSetSliceWithCells failed: {reprStr e}"

private def mkDictSliceRoot2 (k1 : BitString) (v1 : Slice) (k2 : BitString) (v2 : Slice) : Cell :=
  match dictSetSliceWithCells (some (mkDictSliceRoot k1 v1)) k2 v2 .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _ok, _created, _loaded) =>
      panic! "failed to build two-entry dict root: insertion returned none"
  | .error e =>
      panic! s!"dictSetSliceWithCells failed: {reprStr e}"

private def intSignedRoot4SingleNeg1 : Cell :=
  mkDictSliceRoot (keyBitsFor (-1) 4 false) valueSliceA

private def intSignedRoot4Single2 : Cell :=
  mkDictSliceRoot (keyBitsFor 2 4 false) valueSliceB

private def intSignedRoot4 : Cell :=
  mkDictSliceRoot2 (keyBitsFor (-1) 4 false) valueSliceA (keyBitsFor 2 4 false) valueSliceB

private def intSignedRoot4Zero : Cell :=
  mkDictSliceRoot (keyBitsFor 0 0 false) valueSliceC

private def intSignedBadBitsRoot4 : Cell :=
  mkDictSliceRoot (keyBitsFor 3 4 false) valueSliceBits

private def intSignedBadTwoRefsRoot4 : Cell :=
  mkDictSliceRoot (keyBitsFor 1 4 false) valueSliceTwoRefs

private def intSignedBadNoRefRoot4 : Cell :=
  mkDictSliceRoot (keyBitsFor 5 4 false) (mkSliceFromBits #[])

private def mkIntCaseStack (root : Value) (key : Int) (n : Int) : Array Value :=
  #[root, intV key, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIdelGetId
    codeCell? := some dictIdelGetCode
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
    instr := dictIdelGetId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictIDelGetDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt dictIdelGetInstr stack

private def runDictIDelGetFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.tonEnvOp .setGasLimit) (VM.push (intV dispatchSentinel)) stack

private def dictIdelGetGas : Int :=
  computeExactGasBudget dictIdelGetInstr

private def dictIdelGetGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictIdelGetInstr

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

private def genDICTIDELGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    (mkCase s!"fuzz/hit/single-neg1/{tag}" (mkIntCaseStack (.cell intSignedRoot4SingleNeg1) (-1) 4), rng2)
  else if shape = 1 then
    (mkCase s!"fuzz/hit/single-two/{tag}" (mkIntCaseStack (.cell intSignedRoot4Single2) 2 4), rng2)
  else if shape = 2 then
    (mkCase s!"/fuzz/hit/two-entry/{tag}" (mkIntCaseStack (.cell intSignedRoot4) (-1) 4), rng2)
  else if shape = 3 then
    (mkCase s!"fuzz/miss/null-root/{tag}" (mkIntCaseStack .null 7 4), rng2)
  else if shape = 4 then
    (mkCase s!"fuzz/miss/non-empty/{tag}" (mkIntCaseStack (.cell intSignedRoot4) 7 4), rng2)
  else if shape = 5 then
    (mkCase s!"fuzz/miss/zero-key/{tag}" (mkIntCaseStack (.cell intSignedRoot4Zero) 2 0), rng2)
  else if shape = 6 then
    (mkCase s!"fuzz/payload/bits/{tag}" (mkIntCaseStack (.cell intSignedBadBitsRoot4) 3 4), rng2)
  else if shape = 7 then
    (mkCase s!"fuzz/payload/two-refs/{tag}" (mkIntCaseStack (.cell intSignedBadTwoRefsRoot4) 1 4), rng2)
  else if shape = 8 then
    (mkCase s!"fuzz/payload/no-ref/{tag}" (mkIntCaseStack (.cell intSignedBadNoRefRoot4) 5 4), rng2)
  else if shape = 9 then
    (mkCase s!"fuzz/underflow/empty/{tag}" #[], rng2)
  else if shape = 10 then
    (mkCase s!"fuzz/underflow/two-items/{tag}" #[.cell intSignedRoot4, intV 7], rng2)
  else if shape = 11 then
    (mkCase s!"/fuzz/type/key-non-int/{tag}" #[.cell intSignedRoot4, .slice (Slice.ofCell sampleCellC), intV 4], rng2)
  else if shape = 12 then
    let (badKey, rng3) := pickInt257OutOfRange rng2
    (mkCase s!"/fuzz/range/key-out-of-range/{tag}" (mkIntCaseStack (.cell intSignedRoot4) badKey 4), rng3)
  else if shape = 13 then
    (mkCase s!"fuzz/range/n-negative/{tag}" (mkIntCaseStack (.cell intSignedRoot4) 2 (-1)), rng2)
  else if shape = 14 then
    (mkCase s!"/fuzz/range/n-too-large/{tag}" (mkIntCaseStack (.cell intSignedRoot4) 2 1024), rng2)
  else if shape = 15 then
    (mkCaseCode (s!"fuzz/decode/below/{tag}") #[] (rawCell16 0xf461), rng2)
  else if shape = 16 then
    (mkCaseCode (s!"fuzz/decode/above/{tag}") #[] (rawCell16 0xf468), rng2)
  else if shape = 17 then
    (mkCaseCode (s!"/fuzz/decode/truncated-8/{tag}") #[] (Cell.mkOrdinary (natToBits 0xf4 8) #[]), rng2)
  else if shape = 18 then
    (mkCase s!"/fuzz/gas/exact/{tag}" (mkIntCaseStack .null 7 4) (oracleGasLimitsExact dictIdelGetGas), rng2)
  else if shape = 19 then
    (mkCase (s!"fuzz/gas/exact-minus-one/{tag}") (mkIntCaseStack .null 7 4)
      (oracleGasLimitsExactMinusOne dictIdelGetGasMinusOne), rng2)
  else
    (mkCase s!"fuzz/malformed-root/{tag}" (mkIntCaseStack (.cell malformedRoot) 7 4), rng2)

def suite : InstrSuite where
  id := dictIdelGetId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/fallback" (runDictIDelGetFallback #[]) #[intV dispatchSentinel]
    },
    { name := "unit/runtime/hit/single-neg1"
      run := do
        expectOkStack "runtime/hit/single-neg1"
          (runDictIDelGetDirect (mkIntCaseStack (.cell intSignedRoot4SingleNeg1) (-1) 4))
          #[.null, .slice valueSliceA, intV (-1)]
    },
    { name := "unit/runtime/hit/single-two"
      run := do
        expectOkStack "runtime/hit/single-two"
          (runDictIDelGetDirect (mkIntCaseStack (.cell intSignedRoot4Single2) 2 4))
          #[.null, .slice valueSliceB, intV (-1)]
    },
    { name := "unit/runtime/miss/null-root"
      run := do
        expectOkStack "runtime/miss/null-root"
          (runDictIDelGetDirect (mkIntCaseStack .null 7 4))
          #[.null, intV 0]
    },
    { name := "unit/runtime/miss/non-empty-root"
      run := do
        expectOkStack "runtime/miss/non-empty-root"
          (runDictIDelGetDirect (mkIntCaseStack (.cell intSignedRoot4) 7 4))
          #[.cell intSignedRoot4, intV 0]
    },
    { name := "unit/runtime/payload-with-bits"
      run := do
        expectOkStack "runtime/payload-with-bits"
          (runDictIDelGetDirect (mkIntCaseStack (.cell intSignedBadBitsRoot4) 3 4))
          #[.null, .slice valueSliceBits, intV (-1)]
    },
    { name := "unit/runtime/payload/no-ref"
      run := do
        expectOkStack "runtime/payload/no-ref"
          (runDictIDelGetDirect (mkIntCaseStack (.cell intSignedBadNoRefRoot4) 5 4))
          #[.null, .slice (mkSliceFromBits #[]), intV (-1)]
    },
    { name := "unit/runtime/payload/two-refs"
      run := do
        expectOkStack "runtime/payload/two-refs"
          (runDictIDelGetDirect (mkIntCaseStack (.cell intSignedBadTwoRefsRoot4) 1 4))
          #[.null, .slice valueSliceTwoRefs, intV (-1)]
    },
    { name := "unit/runtime/underflow/empty"
      run := do
        expectErr "runtime/underflow-empty" (runDictIDelGetDirect #[]) .stkUnd
    },
    { name := "unit/runtime/underflow/two-items"
      run := do
        expectErr "runtime/underflow-two-items" (runDictIDelGetDirect #[.cell intSignedRoot4, intV 2]) .stkUnd
    },
    { name := "unit/runtime/underflow/one-item"
      run := do
        expectErr "runtime/underflow-one-item" (runDictIDelGetDirect #[.cell intSignedRoot4, intV 3]) .stkUnd
    },
    { name := "unit/runtime/type/n-non-int"
      run := do
        expectErr "runtime/type-non-int" (runDictIDelGetDirect #[(.cell intSignedRoot4), intV (-1), .slice (Slice.ofCell sampleCellA)]) .typeChk
    },
    { name := "unit/runtime/type/dict-not-cell"
      run := do
        expectErr "runtime/type-dict-not-cell" (runDictIDelGetDirect #[intV 4, intV 2, intV 4]) .typeChk
    },
    { name := "unit/runtime/type/key-not-int"
      run := do
        expectErr "runtime/type-key-not-int" (runDictIDelGetDirect #[.cell intSignedRoot4, .slice (Slice.ofCell sampleCellA), intV 4]) .typeChk
    },
    { name := "unit/runtime/range/n-negative"
      run := do
        expectErr "runtime/range-n-negative" (runDictIDelGetDirect #[.cell intSignedRoot4, intV 2, intV (-1)]) .rangeChk
    },
    { name := "unit/runtime/range/n-too-large"
      run := do
        expectErr "runtime/range-n-too-large" (runDictIDelGetDirect #[.cell intSignedRoot4, intV 2, intV 1024]) .rangeChk
    },
    { name := "unit/runtime/range/key-high"
      run := do
        expectErr "runtime/range-key-high" (runDictIDelGetDirect #[.cell intSignedRoot4, intV 8, intV 4]) .rangeChk
    },
    { name := "unit/runtime/range/key-low"
      run := do
        expectErr "runtime/range-key-low" (runDictIDelGetDirect #[.cell intSignedRoot4, intV (-9), intV 4]) .rangeChk
    },
    { name := "unit/runtime/range/key-nan"
      run := do
        expectErr "runtime/range-key-nan" (runDictIDelGetDirect #[.cell intSignedRoot4, .int .nan, intV 4]) .rangeChk
    },
    { name := "unit/decode/target"
      run := do
        expectDecodeOk "decode/target" dictIdelGetCode dictIdelGetInstr
    },
    { name := "unit/decode/neighbor-slice"
      run := do
        expectDecodeOk "decode/neighbor-slice" dictIDelGetNeighborSliceCode (.dictExt (.mutGet false false false .del))
    },
    { name := "unit/decode/neighbor-signed-ref"
      run := do
        expectDecodeOk "decode/neighbor-signed-ref" dictIDelGetNeighborByRefCode (.dictExt (.mutGet true false true .del))
    },
    { name := "unit/decode/neighbor-unsigned"
      run := do
        expectDecodeOk "decode/neighbor-unsigned" dictIDelGetNeighborUnsignedCode (.dictExt (.mutGet true true false .del))
    },
    { name := "unit/decode/neighbor-unsigned-ref"
      run := do
        expectDecodeOk "decode/neighbor-unsigned-ref" dictIDelGetNeighborUnsignedRefCode (.dictExt (.mutGet true true true .del))
    },
    { name := "unit/decode/underbound"
      run := do
        expectDecodeErr "decode/underbound" (rawCell16 0xf461) .invOpcode
    },
    { name := "unit/decode/overbound"
      run := do
        expectDecodeErr "decode/overbound" (rawCell16 0xf468) .invOpcode
    },
    { name := "unit/decode/truncated-8"
      run := do
        expectDecodeErr "decode/truncated-8" (Cell.mkOrdinary (natToBits 0xf4 8) #[]) .invOpcode
    },
    { name := "unit/decode/truncated-15"
      run := do
        expectDecodeErr "decode/truncated-15" (Cell.mkOrdinary (natToBits (0xf464 >>> 1) 15) #[]) .invOpcode
    },
    { name := "unit/assemble/unsupported"
      run := do
        expectAssembleErr "assemble/unsupported" dictIdelGetInstr .invOpcode
    }
  ]
  oracle := #[
    -- [B1] matched opcode dispatch path with single signed hit.
    mkCase "oracle/hit/single-neg1" (mkIntCaseStack (.cell intSignedRoot4SingleNeg1) (-1) 4),
    -- [B5] matched opcode dispatch path with single signed hit and different key.
    mkCase "oracle/hit/single-two" (mkIntCaseStack (.cell intSignedRoot4Single2) 2 4),
    -- [B5] hit path with two-entry root.
    mkCase "oracle/hit/two-entry" (mkIntCaseStack (.cell intSignedRoot4) (-1) 4),
    -- [B5] hit path with zero-length key on n=0 root.
    mkCase "oracle/hit/zero-key" (mkIntCaseStack (.cell intSignedRoot4Zero) 0 0),
    -- [B5] miss path in null root.
    mkCase "oracle/miss/null" (mkIntCaseStack .null 7 4),
    -- [B5] miss path in non-empty root.
    mkCase "oracle/miss/non-empty" (mkIntCaseStack (.cell intSignedRoot4) 7 4),
    -- [B5] miss path with key not matching known branch.
    mkCase "oracle/miss/non-match" (mkIntCaseStack (.cell intSignedRoot4) 0 4),
    -- [B2] empty stack underflow.
    mkCase "oracle/underflow/empty" #[],
    -- [B2] one-item underflow.
    mkCase "oracle/underflow/one-item" #[.cell intSignedRoot4],
    -- [B2] two-item underflow.
    mkCase "oracle/underflow/two-items" #[.cell intSignedRoot4, intV 7],
    -- [B3] n non-int type path.
    mkCase "oracle/type/n-non-int" #[.cell intSignedRoot4, intV (-1), .slice (Slice.ofCell sampleCellA)],
    -- [B3] dict root type-check error.
    mkCase "oracle/type/dict-not-cell" #[intV 4, intV 2, intV 4],
    -- [B3] key type-check error.
    mkCase "oracle/type/key-not-int" #[.cell intSignedRoot4, .slice (Slice.ofCell sampleCellA), intV 4],
    -- [B4] negative n.
    mkCase "oracle/range/n-negative" #[.cell intSignedRoot4, intV 2, intV (-1)],
    -- [B4] too-large n.
    mkCase "oracle/range/n-too-large" #[.cell intSignedRoot4, intV 2, intV 1024],
    -- [B4] too-large signed key (Lean range check branch).
    mkCase "oracle/range/key-high" #[.cell intSignedRoot4, intV 8, intV 4],
    -- [B4] too-small signed key (Lean range check branch).
    mkCase "oracle/range/key-low" #[.cell intSignedRoot4, intV (-9), intV 4],
    -- [B4] NaN key.
    mkCase "oracle/range/key-nan" #[.cell intSignedRoot4, .int .nan, intV 4],
    -- [B4] key out-of-range by generator pool (should hit Lean/Reference boundary).
    mkCase "oracle/range/key-out-of-range-generated" (mkIntCaseStack (.cell intSignedRoot4) 99 4),
    -- [B6] malformed root shape should raise.
    mkCase "oracle/err/malformed-root" (mkIntCaseStack (.cell malformedRoot) 7 4),
    -- [B7] payload values with raw bits survive non-ref path.
    mkCase "oracle/payload/bits" (mkIntCaseStack (.cell intSignedBadBitsRoot4) 3 4),
    -- [B7] payload with no bits survives non-ref path.
    mkCase "oracle/payload/no-ref" (mkIntCaseStack (.cell intSignedBadNoRefRoot4) 5 4),
    -- [B7] payload with two refs survives non-ref path.
    mkCase "oracle/payload/two-refs" (mkIntCaseStack (.cell intSignedBadTwoRefsRoot4) 1 4),
    -- [B8] direct opcode decode target.
    mkCaseCode "oracle/decode/target" #[] dictIdelGetCode,
    -- [B8] decode signed-ref neighbor.
    mkCaseCode "oracle/decode/neighbor-signed-ref" #[] dictIDelGetNeighborByRefCode,
    -- [B8] decode unsigned neighbor.
    mkCaseCode "oracle/decode/neighbor-unsigned" #[] dictIDelGetNeighborUnsignedCode,
    -- [B8] decode unsigned-ref neighbor.
    mkCaseCode "oracle/decode/neighbor-unsigned-ref" #[] dictIDelGetNeighborUnsignedRefCode,
    -- [B8] decode lower boundary failure.
    mkCaseCode "oracle/decode/below" #[] (rawCell16 0xf461),
    -- [B8] decode upper boundary failure.
    mkCaseCode "oracle/decode/above" #[] (rawCell16 0xf468),
    -- [B8] decode truncated 8-bit failure.
    mkCaseCode "oracle/decode/truncated-8" #[] (Cell.mkOrdinary (natToBits 0xf4 8) #[]),
    -- [B8] decode truncated 15-bit failure.
    mkCaseCode "oracle/decode/truncated-15" #[] (Cell.mkOrdinary (natToBits (0xf464 >>> 1) 15) #[]),
    -- [B9] exact budget with miss path.
    mkCase "oracle/gas/exact/miss" (mkIntCaseStack .null 7 4) (oracleGasLimitsExact dictIdelGetGas),
    -- [B9] exact-minus-one budget should fail before success.
    mkCase "oracle/gas/exact-minus-one/miss" (mkIntCaseStack .null 7 4)
      (oracleGasLimitsExactMinusOne dictIdelGetGasMinusOne)
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr dictIdelGetId
      count := 500
      gen := genDICTIDELGETFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIDELGET
