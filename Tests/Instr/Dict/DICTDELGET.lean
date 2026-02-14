import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTDELGET

/-
INSTRUCTION: DICTDELGET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path:
   - `execInstrDictExt` only handles `.dictExt (.mutGet ...)`, while `.dictExt` has no other matching branch.
   - Any opcode decoded as non-`dictExt` should follow `next`.

2. [B2] Runtime stack-shape/underflow branch:
   - `VM.checkUnderflow (if mode==.del then 3 else 4)` is used by all mutGet paths.
   - DICTDELGET requires at least 3 items: `(n : Nat)`, `(dict : Option Cell)`, `(key : Slice | Int)` depending on `intKey`.
   - Underflow errors are `stkUnd`.

3. [B3] Runtime key-extraction branch (slice keys):
   - For slice keys, `popSlice` then `haveBits n`.
   - If not enough bits in key slice: `cellUnd`.
   - When key is present in dict, old value is removed and returned.
   - When key is absent, old value is not found and only `false` is pushed with root updated.

4. [B4] Runtime key-extraction branch (int keys):
   - For integer keys, integer validation is `dictKeyBits? idx n unsigned`.
   - Out-of-range signed/unsigned values currently route to `.rangeChk` in Lean.
   - C++ reference handles unsigned/signed overflow as key-not-found (`false`), which is a behavioral difference to be tracked.

5. [B5] Reference-return variant and payload shape checks:
   - `byRef=false` pushes `.slice oldVal`.
   - `byRef=true` calls `extractRefOrThrow oldVal`.
   - `extractRefOrThrow` succeeds only for value-slices with `size = 0` and `refs = 1`.
   - Invalid payloads (bits, zero refs, or >1 ref) raise `dictErr`.

6. [B6] Error propagation and dictionary traversal:
   - All delete operations run `dictDeleteWithCells`, with `(ok,newRoot,created,loaded)` handling.
   - Traversal loads and visited-cell accounting happens before exceptions and on all successful paths.
   - `dictDeleteWithCells` path errors propagate as thrown exceptions.

7. [B7] Assembler/encoding branch:
   - `TvmLean/Model/Instr/Asm/Cp0.lean` cannot encode `.dictExt`, returning `.invOpcode`.
   - Only `Codepage` decode supports this form.

8. [B8] Decoder branch (opcode map):
   - `dictExt (.mutGet ...)` for DELGET is decoded from `0xf462..0xf467`.
   - Bit fields:
     - `byRef := w & 1`
     - `intKey := w & 4`
     - `unsigned := intKey ∧ (w & 2)`
   - `0xf461` and `0xf468` should not decode to `DICTDELGET` (decoder boundary behavior is explicit).

9. [B9] Gas accounting branches:
   - Static base gas: `instrGas` of `.dictExt (.mutGet ...)` contributes `instrGas`.
   - Dynamic penalty exists via `consumeCreatedGas created`; delete paths can rewire and rebuild nodes.
   - There are therefore base-gas and gas-minus-one cases for non-creating miss-paths, plus merge-delete paths with potentially additional gas.

TOTAL BRANCHES: 9
Each oracle test below is tagged with the branch(es) it covers.
-/

private def dictDelGetId : InstrId := { name := "DICTDELGET" }

private def dictDelGetInstr (intKey unsigned byRef : Bool) : Instr :=
  .dictExt (.mutGet intKey unsigned byRef .del)

private def dictDelGetCode (intKey unsigned byRef : Bool) : Nat :=
  0xf462 ||| (if intKey then 4 else 0) ||| (if unsigned then 2 else 0) ||| (if byRef then 1 else 0)

private def dictDelGetCell (intKey unsigned byRef : Bool) : Cell :=
  Cell.mkOrdinary (natToBits (dictDelGetCode intKey unsigned byRef) 16) #[]

private def dictDelGetSliceCode : Cell :=
  dictDelGetCell false false false

private def dictDelGetSliceRefCode : Cell :=
  dictDelGetCell false false true

private def dictDelGetIntSignedCode : Cell :=
  dictDelGetCell true false false

private def dictDelGetIntSignedRefCode : Cell :=
  dictDelGetCell true false true

private def dictDelGetIntUnsignedCode : Cell :=
  dictDelGetCell true true false

private def dispatchSentinel : Int := 99221

private def rawCell16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawCell8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def sampleCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def sampleCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x3b 8) #[]

private def sampleCellC : Cell :=
  Cell.mkOrdinary (natToBits 0x17 8) #[]

private def valueLeafA : Cell :=
  sampleCellA

private def valueLeafB : Cell :=
  sampleCellB

private def valueLeafC : Cell :=
  sampleCellC

private def valueCellWithBits : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def valueCellWithBitsAndRef : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[sampleCellA]

private def valueCellTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[sampleCellA, sampleCellB]

private def valueCellZeroBitsNoRef : Cell :=
  Cell.mkOrdinary #[] #[]

private def valueSliceA : Slice :=
  Slice.ofCell valueLeafA

private def valueSliceB : Slice :=
  Slice.ofCell valueLeafB

private def valueSliceC : Slice :=
  Slice.ofCell valueLeafC

private def makeSlice (bits : BitString) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits #[])

private def keyBitsFor (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bs => bs
  | none =>
      panic! s!"expected key bits for idx={idx}, n={n}, unsigned={unsigned}"

private def mkDictSliceRoot (key : BitString) (value : Slice) : Cell :=
  match dictSetSliceWithCells none key value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | _ => panic! "failed to build single-entry slice dict"

private def mkDictSliceRoot2 (k1 : BitString) (v1 : Slice) (k2 : BitString) (v2 : Slice) : Cell :=
  match dictSetSliceWithCells none k1 v1 .set with
  | .ok (some root1, _ok1, _created1, _loaded1) =>
      match dictSetSliceWithCells (some root1) k2 v2 .set with
      | .ok (some root2, _ok2, _created2, _loaded2) => root2
      | _ => panic! "failed to build second-entry slice dict"
  | _ => panic! "failed to build first-entry slice dict"

private def mkDictRefRoot (key : BitString) (value : Cell) : Cell :=
  match dictSetRefWithCells none key value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | _ => panic! "failed to build single-entry ref dict"

private def mkDictRefRoot2 (k1 : BitString) (v1 : Cell) (k2 : BitString) (v2 : Cell) : Cell :=
  match dictSetRefWithCells none k1 v1 .set with
  | .ok (some root1, _ok1, _created1, _loaded1) =>
      match dictSetRefWithCells (some root1) k2 v2 .set with
      | .ok (some root2, _ok2, _created2, _loaded2) => root2
      | _ => panic! "failed to build second-entry ref dict"
  | _ => panic! "failed to build first-entry ref dict"

private def sliceRootMissingBase : Cell :=
  mkDictSliceRoot2 (natToBits 2 4) valueSliceA (natToBits 3 4) valueSliceB

private def sliceRootSingle4 : Cell :=
  mkDictSliceRoot (natToBits 2 4) valueSliceA

private def sliceRootSingleRef4 : Cell :=
  mkDictRefRoot (natToBits 2 4) sampleCellC

private def sliceRootRefBadBits4 : Cell :=
  mkDictSliceRoot (natToBits 2 4) (Slice.ofCell valueCellWithBits)

private def sliceRootRefBadTwoRefs4 : Cell :=
  mkDictSliceRoot (natToBits 2 4) (Slice.ofCell valueCellTwoRefs)

private def sliceRootRefBadEmpty4 : Cell :=
  mkDictSliceRoot (natToBits 2 4) (Slice.ofCell valueCellZeroBitsNoRef)

private def intSignedRoot4 : Cell :=
  mkDictSliceRoot2
    (keyBitsFor (-3) 4 false) valueSliceA
    (keyBitsFor 4 4 false) valueSliceB

private def intUnsignedRoot4 : Cell :=
  mkDictSliceRoot2
    (keyBitsFor 5 4 true) valueSliceA
    (keyBitsFor 9 4 true) valueSliceB

private def intSignedRefRoot4 : Cell :=
  mkDictRefRoot (keyBitsFor (-1) 4 false) sampleCellA

private def intUnsignedRefRoot4 : Cell :=
  mkDictRefRoot (keyBitsFor 10 4 true) sampleCellB

private def mkSliceCaseStack (root : Value) (n : Int) (keyBits : BitString) : Array Value :=
  #[root, .slice (makeSlice keyBits), intV n]

private def mkIntCaseStack (root : Value) (n : Int) (key : Int) : Array Value :=
  #[root, intV key, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelGetId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseProg
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelGetId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, rest) =>
      if instr != expected || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: unexpected decode result {reprStr instr}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembly error {expected}, got success")

private def runDictDelGetFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV dispatchSentinel)) stack

private def runDictDelGetDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def dictDelGetBaseGas : Int :=
  instrGas (dictDelGetInstr false false false) 16

private def dictDelGetGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictDelGetBaseGas

private def dictDelGetGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictDelGetBaseGas

private def fuzzValuePool : Array Value :=
  #[
    .null,
    .cell sampleCellA,
    .cell sampleCellB,
    .slice (makeSlice (natToBits 5 3)),
    .slice (makeSlice (natToBits 42 7)),
    intV (-1),
    intV 0,
    intV 1,
    intV 7,
    intV maxInt257
  ]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def randomSliceKey (n : Nat) (rng0 : StdGen) : Slice × StdGen :=
  if n = 0 then
    (makeSlice #[], rng0)
  else
    let (bs, rng1) := randBitString n rng0
    (makeSlice bs, rng1)

private def genDictDelGetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (keyVal, rng2) := randNat rng1 0 15
    let keyBits := natToBits keyVal 4
    let stack := mkSliceCaseStack (.cell sliceRootSingle4) 4 keyBits
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/slice-hit/{tag}" stack dictDelGetSliceCode, rng3)
  else if shape = 1 then
    let (keyVal, rng2) := randNat rng1 0 15
    let keyBits := natToBits keyVal 5
    let stack := mkSliceCaseStack (.null) 5 keyBits
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/slice-miss-empty/{tag}" stack dictDelGetSliceCode, rng3)
  else if shape = 2 then
    let (bits, rng2) := randNat rng1 0 15
    let (shortBits, rng3) := randNat rng2 0 3
    let stack := mkSliceCaseStack (.cell sliceRootSingle4) 8 (natToBits bits shortBits)
    let (tag, rng4) := randNat rng3 0 999_999
    (mkCase s!"fuzz/slice-key-underflow/{tag}" stack dictDelGetSliceCode, rng4)
  else if shape = 3 then
    let (i, rng2) := randNat rng1 0 3
    let k : Int := if i = 0 then -3 else if i = 1 then 4 else if i = 2 then -1 else 6
    let stack := mkIntCaseStack (.cell intSignedRoot4) 4 k
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/int-signed-hit/{tag}" stack dictDelGetIntSignedCode, rng3)
  else if shape = 4 then
    let (i, rng2) := randNat rng1 0 3
    let k : Int := if i = 0 then 5 else if i = 1 then 9 else if i = 2 then 12 else 0
    let stack := mkIntCaseStack (.cell intUnsignedRoot4) 4 k
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/int-unsigned-hit/{tag}" stack dictDelGetIntUnsignedCode, rng3)
  else if shape = 5 then
    let (k, rng2) := pickInt257OutOfRange rng1
    let stack := mkIntCaseStack (.cell intSignedRoot4) 4 k
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/int-signed-out-of-range/{tag}" stack dictDelGetIntSignedCode, rng3)
  else if shape = 6 then
    let (k, rng2) := pickInt257OutOfRange rng1
    let stack := mkIntCaseStack (.cell intUnsignedRoot4) 4 k
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/int-unsigned-out-of-range/{tag}" stack dictDelGetIntUnsignedCode, rng3)
  else if shape = 7 then
    let (i, rng3) := randNat rng1 0 1
    let k : Int := if i = 0 then -1 else 1
    let stack := mkIntCaseStack (.cell intSignedRefRoot4) 4 k
    let (tag, rng4) := randNat rng3 0 999_999
    (mkCase s!"fuzz/ref-hit/{tag}" stack dictDelGetIntSignedRefCode, rng4)
  else if shape = 8 then
    let (v, rng2) := pickFromPool fuzzValuePool rng1
    let stack := #[v, .null, intV 4]
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/underflow/{tag}" stack dictDelGetSliceCode, rng3)
  else if shape = 9 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase s!"fuzz/decode-below/{tag}" #[] (rawCell16 0xf461), rng2)
  else if shape = 10 then
    let (tag, rng3) := randNat rng1 0 999_999
    let stack := mkSliceCaseStack (.cell sliceRootRefBadBits4) 4 (natToBits 2 4)
    (mkCase s!"fuzz/ref-payload-dicterr/{tag}" stack dictDelGetSliceRefCode, rng3)
  else
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase s!"fuzz/decode-above/{tag}" #[] (rawCell16 0xf468), rng2)

def suite : InstrSuite where
  id := dictDelGetId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch-fallback" (runDictDelGetFallback (.add) #[]) #[intV dispatchSentinel]
    },
    { name := "unit/dispatch/matched-empty"
      run := do
        expectErr "dispatch-matched-empty" (runDictDelGetDirect (dictDelGetInstr false false false) #[.null, intV 7, intV 0]) .cellUnd
    },
    { name := "unit/decode/slice-non-ref"
      run := do
        expectDecodeOk "decode-slice-non-ref" dictDelGetSliceCode (dictDelGetInstr false false false)
    },
    { name := "unit/decode/int-signed-ref"
      run := do
        expectDecodeOk "decode-int-signed-ref" dictDelGetIntSignedRefCode (dictDelGetInstr true false true)
    },
    { name := "unit/decode/int-unsigned"
      run := do
        expectDecodeOk "decode-int-unsigned" dictDelGetIntUnsignedCode (dictDelGetInstr true true false)
    },
    { name := "unit/decode/below-range"
      run := do
        expectDecodeErr "decode-below-range" (rawCell16 0xf461) .invOpcode
    },
    { name := "unit/decode/above-range"
      run := do
        expectDecodeErr "decode-above-range" (rawCell16 0xf468) .invOpcode
    },
    { name := "unit/asm/dictext-rejected"
      run := do
        expectAssembleErr "asm/rejected" (dictDelGetInstr false false false) .invOpcode
    }
  ]
  oracle :=
    #[
      -- [B1] slice branch miss path on empty dictionary.
      mkCase "oracle/slice/not-found-empty" (mkSliceCaseStack .null 4 (natToBits 2 4)) dictDelGetSliceCode,

      -- [B1] slice branch hit path with one existing entry.
      mkCase "oracle/slice/hit-single-key" (mkSliceCaseStack (.cell sliceRootSingle4) 4 (natToBits 2 4)) dictDelGetSliceCode,

      -- [B1] slice branch hit path with multi-entry root (shared branch).
      mkCase "oracle/slice/hit-multi-root" (mkSliceCaseStack (.cell sliceRootMissingBase) 4 (natToBits 2 4)) dictDelGetSliceCode,

      -- [B1] slice branch miss path with unrelated key in non-empty dictionary.
      mkCase "oracle/slice/miss-non-empty" (mkSliceCaseStack (.cell sliceRootSingle4) 4 (natToBits 15 4)) dictDelGetSliceCode,

      -- [B1] slice branch hit path with n=0 empty key bit-string.
      mkCase "oracle/slice/hit-n0-key" (mkSliceCaseStack (.cell sliceRootSingle4) 0 #[]) dictDelGetSliceCode,

      -- [B2] integer signed branch hit (negative key).
      mkCase "oracle/int/signed/hit-negative" (mkIntCaseStack (.cell intSignedRoot4) 4 (-3)) dictDelGetIntSignedCode,

      -- [B2] integer signed branch hit (positive key).
      mkCase "oracle/int/signed/hit-positive" (mkIntCaseStack (.cell intSignedRoot4) 4 (4)) dictDelGetIntSignedCode,

      -- [B2] integer signed branch miss.
      mkCase "oracle/int/signed/miss" (mkIntCaseStack (.cell intSignedRoot4) 4 (6)) dictDelGetIntSignedCode,

      -- [B2] integer unsigned branch hit.
      mkCase "oracle/int/unsigned/hit" (mkIntCaseStack (.cell intUnsignedRoot4) 4 (5)) dictDelGetIntUnsignedCode,

      -- [B2] integer unsigned branch miss.
      mkCase "oracle/int/unsigned/miss" (mkIntCaseStack (.cell intUnsignedRoot4) 4 (0)) dictDelGetIntUnsignedCode,

      -- [B3] byRef slice branch hit and value extracted as ref.
      mkCase "oracle/byref/slice-hit" (mkSliceCaseStack (.cell sliceRootSingleRef4) 4 (natToBits 2 4)) dictDelGetSliceRefCode,

      -- [B3] byRef int signed hit branch.
      mkCase "oracle/byref/int-signed-hit" (mkIntCaseStack (.cell intSignedRefRoot4) 4 (-1)) dictDelGetIntSignedRefCode,

      -- [B3] byRef int unsigned hit branch.
      mkCase "oracle/byref/int-unsigned-hit" (mkIntCaseStack (.cell intUnsignedRefRoot4) 4 (10)) dictDelGetIntUnsignedCode,

      -- [B5] byRef payload is slice with non-empty bits -> expected dictErr.
      mkCase "oracle/byref/payload/bits" (mkSliceCaseStack (.cell sliceRootRefBadBits4) 4 (natToBits 2 4)) dictDelGetSliceRefCode,

      -- [B5] byRef payload is non-ref empty slice -> expected dictErr.
      mkCase "oracle/byref/payload/no-ref" (mkSliceCaseStack (.cell sliceRootRefBadEmpty4) 4 (natToBits 2 4)) dictDelGetSliceRefCode,

      -- [B5] byRef payload has multiple refs -> expected dictErr.
      mkCase "oracle/byref/payload/two-refs" (mkSliceCaseStack (.cell sliceRootRefBadTwoRefs4) 4 (natToBits 2 4)) dictDelGetSliceRefCode,

      -- [B4] slice key too short for declared length -> cellUnd.
      mkCase "oracle/slice/key-underflow-short4/decl8" (mkSliceCaseStack (.cell sliceRootSingle4) 8 (natToBits 3 4)) dictDelGetSliceCode,

      -- [B4] slice key underflow with n=8 and tiny key slice in byRef mode.
      mkCase "oracle/slice/key-underflow-byref" (mkSliceCaseStack (.cell sliceRootSingle4) 8 (natToBits 1 3)) dictDelGetSliceRefCode,

      -- [B4] n invalid from stack (too large) in slice mode -> rangeChk.
      mkCase "oracle/slice/n-too-large" (mkSliceCaseStack (.cell sliceRootSingle4) 1024 (natToBits 2 8)) dictDelGetSliceCode,

      -- [B4] negative n in slice mode -> rangeChk.
      mkCase "oracle/slice/n-negative" (mkSliceCaseStack (.cell sliceRootSingle4) (-1) (natToBits 2 4)) dictDelGetSliceCode,

      -- [B4] integer signed range overflow should be rangeChk.
      mkCase "oracle/int/signed/out-of-range-high" (mkIntCaseStack (.cell intSignedRoot4) 4 (8)) dictDelGetIntSignedCode,

      -- [B4] integer signed range overflow (too negative).
      mkCase "oracle/int/signed/out-of-range-low" (mkIntCaseStack (.cell intSignedRoot4) 4 (-9)) dictDelGetIntSignedCode,

      -- [B4] integer unsigned negative key -> rangeChk in Lean.
      mkCase "oracle/int/unsigned/negative-key" (mkIntCaseStack (.cell intUnsignedRoot4) 4 (-1)) dictDelGetIntUnsignedCode,

      -- [B4] integer unsigned too-large key -> rangeChk in Lean.
      mkCase "oracle/int/unsigned/out-of-range" (mkIntCaseStack (.cell intUnsignedRoot4) 4 (17)) dictDelGetIntUnsignedCode,

      -- [B2/B4] integer mode underflow when only two stack values remain.
      mkCase "oracle/int/underflow-two-items" #[.cell intSignedRoot4, intV 4] dictDelGetIntSignedCode,

      -- [B2/B4] slice mode underflow when only two stack values remain.
      mkCase "oracle/slice/underflow-two-items" #[.cell sliceRootSingle4, .slice (makeSlice (natToBits 2 4))] dictDelGetSliceCode,

      -- [B2/B4] stack underflow with mixed non-empty payload and no enough depth.
      mkCase "oracle/slice/underflow-with-tail" #[.cell sampleCellA, intV 4] dictDelGetSliceCode,

      -- [B9] dispatch/decoder boundary below family should not decode as DICTDELGET.
      mkCase "oracle/decode/below" #[] (rawCell16 0xf461),

      -- [B9] decode boundary above family should not decode as DICTDELGET.
      mkCase "oracle/decode/above" #[] (rawCell16 0xf468),

      -- [B7] truncated opcode bytes should fail decode/validation in both runtimes.
      mkCase "oracle/decode/truncated-8bit" #[] (rawCell8 0xf4), -- intentionally malformed

      -- [B1] gas exact path: miss-path with exact base budget.
      mkCase "oracle/gas/exact/base-miss" (mkSliceCaseStack .null 4 (natToBits 9 4)) dictDelGetSliceCode dictDelGetGasExact,

      -- [B1] gas exact-minus-one path: miss-path should fail before execution.
      mkCase "oracle/gas/exact-minus-one/base-miss" (mkSliceCaseStack .null 4 (natToBits 9 4)) dictDelGetSliceCode dictDelGetGasExactMinusOne
    ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr dictDelGetId
      count := 500
      gen := genDictDelGetFuzzCase
      mutateOracle := false
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTDELGET
