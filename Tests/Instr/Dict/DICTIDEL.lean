import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIDEL

/-!
INSTRUCTION: DICTIDEL (0xf459)

BRANCH ANALYSIS (Lean + C++ source):

1. [B1] Dispatch:
   - `.dictExt (.del intKey unsigned)` is handled by `execInstrDictExt`.
   - Any non-`dictExt` instruction falls through to `next` (verified via sentinel fallback).

2. [B2] Stack-shape checks (`checkUnderflow 3`):
   - Missing any of `(dict, key, n)` triggers `.stkUnd` in all modes.

3. [B3] Width extraction (`popNatUpTo 1023`):
   - `.nan`, negative, and values `> 1023` for `n` raise `.rangeChk`.
   - Non-integer `n` raises `.typeChk`.

4. [B4] Dictionary operand checks:
   - `popMaybeCell` accepts `.null` and `.cell`.
   - Non-cell/tuple/cont values for dictionary raise `.typeChk`.

5. [B5] Integer-key branch (`intKey = true`):
   - Key must be finite int.
   - Non-finite key → `.rangeChk`.
   - Key/range mismatch via `dictKeyBits?` (`signed`/`unsigned` and `n`) raises `.rangeChk` in Lean.
   - C++ `DICTIDEL` differs by returning miss for out-of-range signed keys; this Lean mismatch is handled explicitly.

6. [B6] Slice-key branch (`intKey = false`):
   - `n` bits are read from key slice.
   - Insufficient bits (`haveBits` false) raise `.cellUnd`.

7. [B7] Delete outcome:
   - If key not found, root is unchanged and stack gets `false` (`0`).
   - If found, value is removed and stack gets `true` (`-1`) with rebuilt root.
   - Root may become `.null`.
   - All paths use `dictDeleteWithCells` and return old value only for `mutGet` variants; here only boolean remains.

8. [B8] Error propagation in dictionary traversal:
   - `dictDeleteWithCells` malformed-root errors are propagated after root-load registration (`.dictErr`, `.cellUnd`, etc).

9. [B9] Assembler behavior:
   - `.dictExt` is unsupported by `assembleCp0` and must return `.invOpcode`.

10. [B10] Decoder boundaries:
   - Signed/slice mode: `0xf459`.
   - Signed-int mode: `0xf45a`.
   - Unsigned-int mode: `0xf45b`.
   - `0xf458` and `0xf45c` are decoder errors (`.invOpcode`), and truncated inputs reject decode.

11. [B11] Gas behavior:
   - Exact budget success on miss/hit paths when budget is sufficient.
   - Exact budget minus one should fail.
   - Hit path gas may include `cellCreateGasPrice * created`.

TOTAL BRANCHES: 11.
Each oracle test below is tagged with the branch(es) it exercises.
-/

private def dictDelId : InstrId :=
  { name := "DICTIDEL" }

private def instrSlice : Instr :=
  .dictExt (.del false false)

private def instrIntSigned : Instr :=
  .dictExt (.del true false)

private def instrIntUnsigned : Instr :=
  .dictExt (.del true true)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def instrSliceCode : Cell := raw16 0xf459
private def instrIntSignedCode : Cell := raw16 0xf45a
private def instrIntUnsignedCode : Cell := raw16 0xf45b

private def dispatchSentinel : Int := 7007

private def valueA : Slice := mkSliceFromBits (natToBits 0xa1 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xb2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xc3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xd4 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xe5 8)

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (key, value) := entry
      let keyBits :=
        match dictKeyBits? key n false with
        | some bits => bits
        | none =>
            panic! s!"{label}: invalid key {key} for n={n}"
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting key {key}"
      | .error e =>
          panic! s!"{label}: dict set failed with {e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def mkDictSetUnsignedSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (key, value) := entry
      let keyBits :=
        match dictKeyBits? key n true with
        | some bits => bits
        | none =>
            panic! s!"{label}: invalid key {key} for n={n}"
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting key {key}"
      | .error e =>
          panic! s!"{label}: dict set failed with {e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def dictSliceSignedN8One : Cell :=
  mkDictSetSliceRoot! "dictSliceSignedN8One" 8 #[(7, valueA)]

private def dictSliceSignedN0One : Cell :=
  mkDictSetSliceRoot! "dictSliceSignedN0One" 0 #[(0, valueB)]

private def dictSliceSignedN8Many : Cell :=
  mkDictSetSliceRoot! "dictSliceSignedN8Many" 8 #[(2, valueA), (-3, valueB), (127, valueC)]

private def dictSliceUnsignedN8One : Cell :=
  mkDictSetUnsignedSliceRoot! "dictSliceUnsignedN8One" 8 #[(7, valueD)]

private def dictSliceUnsignedN8Many : Cell :=
  mkDictSetUnsignedSliceRoot! "dictSliceUnsignedN8Many" 8 #[(0, valueE), (255, valueC), (128, valueB)]

private def dictSliceUnsignedN0One : Cell :=
  mkDictSetUnsignedSliceRoot! "dictSliceUnsignedN0One" 0 #[(0, valueD)]

private def malformedDictA : Cell :=
  Cell.mkOrdinary (natToBits 0 1) #[]

private def malformedDictB : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def key7Slice : Slice :=
  mkSliceFromBits (natToBits 7 8)

private def key3ShortSlice : Slice :=
  mkSliceFromBits (natToBits 3 4)

private def key0Slice : Slice :=
  mkSliceFromBits #[] 

private def dictDeleteCreated (root : Cell) (n : Nat) (key : Int) (unsigned : Bool) : Nat :=
  match dictKeyBits? key n unsigned with
  | none => 0
  | some bits =>
      match dictDeleteWithCells (some root) bits with
      | .ok (_, _, created, _) => created
      | .error _ => 0

private def baseGas : Int :=
  computeExactGasBudget instrIntSigned

private def baseGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instrIntSigned

private def hitSignedGas : Int :=
  baseGas + Int.ofNat (dictDeleteCreated dictSliceSignedN8Many 8 127 false) * cellCreateGasPrice

private def hitSignedGasMinusOne : Int :=
  if hitSignedGas > 0 then hitSignedGas - 1 else 0

private def hitUnsignedGas : Int :=
  baseGas + Int.ofNat (dictDeleteCreated dictSliceUnsignedN8Many 8 255 true) * cellCreateGasPrice

private def hitUnsignedGasMinusOne : Int :=
  if hitUnsignedGas > 0 then hitUnsignedGas - 1 else 0

private def gasExact : OracleGasLimits :=
  oracleGasLimitsExact baseGas

private def gasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne baseGasMinusOne

private def gasHitSignedExact : OracleGasLimits :=
  oracleGasLimitsExact hitSignedGas

private def gasHitSignedMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne hitSignedGasMinusOne

private def gasHitUnsignedExact : OracleGasLimits :=
  oracleGasLimitsExact hitUnsignedGas

private def gasHitUnsignedMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne hitUnsignedGasMinusOne

private def mkCaseSigned
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelId
    codeCell? := some instrIntSignedCode
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseUnsigned
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelId
    codeCell? := some instrIntUnsignedCode
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseSlice
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelId
    codeCell? := some instrSliceCode
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
    instr := dictDelId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseProgram
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.add) (VM.push (intV dispatchSentinel)) stack

private def runSigned (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrIntSigned stack

private def runUnsigned (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrIntUnsigned stack

private def runSlice (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrSlice stack

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected end-of-stream decode")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")

private def genDICTIDEL (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    match shape with
    | 0 =>
        (mkCaseSigned "fuzz/signed-hit" #[(.cell dictSliceSignedN8One), intV 7, intV 8], rng1)
    | 1 =>
        (mkCaseSigned "fuzz/signed-miss" #[(.cell dictSliceSignedN8One), intV 9, intV 8], rng1)
    | 2 =>
        (mkCaseSigned "fuzz/signed-empty-root-miss" #[.null, intV 7, intV 8], rng1)
    | 3 =>
        (mkCaseSigned "fuzz/signed-n0-hit" #[(.cell dictSliceSignedN0One), intV 0, intV 0], rng1)
    | 4 =>
        (mkCaseUnsigned "fuzz/unsigned-hit" #[(.cell dictSliceUnsignedN8One), intV 7, intV 8], rng1)
    | 5 =>
        (mkCaseUnsigned "fuzz/unsigned-miss" #[(.cell dictSliceUnsignedN8One), intV 2, intV 8], rng1)
    | 6 =>
        (mkCaseUnsigned "fuzz/unsigned-n0-hit" #[(.cell dictSliceUnsignedN0One), intV 0, intV 0], rng1)
    | 7 =>
        (mkCaseSlice "fuzz/slice-hit" #[(.cell dictSliceSignedN8One), .slice key7Slice, intV 8], rng1)
    | 8 =>
        (mkCaseSlice "fuzz/slice-miss" #[(.cell dictSliceSignedN8One), .slice (mkSliceFromBits (natToBits 2 8)), intV 8], rng1)
    | 9 =>
        (mkCaseSlice "fuzz/slice-underflow" #[(.cell dictSliceSignedN8One), .slice key3ShortSlice, intV 8], rng1)
    | 10 =>
        (mkCaseSigned "fuzz/nan-n" #[(.cell dictSliceSignedN8One), intV 7, .int .nan], rng1)
    | 11 =>
        (mkCaseSigned "fuzz/n-negative" #[(.cell dictSliceSignedN8One), intV 7, intV (-1)], rng1)
    | 12 =>
        (mkCaseSigned "fuzz/n-too-large" #[(.cell dictSliceSignedN8One), intV 7, intV 2000], rng1)
    | 13 =>
        (mkCaseSigned "fuzz/key-range-high" #[(.cell dictSliceSignedN8One), intV 128, intV 8], rng1)
    | 14 =>
        (mkCaseUnsigned "fuzz/key-range-negative" #[(.cell dictSliceUnsignedN8One), intV (-1), intV 8], rng1)
    | 15 =>
        (mkCaseUnsigned "fuzz/key-range-too-large" #[(.cell dictSliceUnsignedN8One), intV 256, intV 8], rng1)
    | 16 =>
        (mkCaseSlice "fuzz/key-type" #[(.cell dictSliceSignedN8One), intV 7, intV 8], rng1)
    | 17 =>
        (mkCaseSigned "fuzz/dict-type" #[intV 7, intV 7, intV 8], rng1)
    | 18 =>
        (mkCaseCode "fuzz/decode-below" #[] (raw16 0xf458), rng1)
    | 19 =>
        (mkCaseCode "fuzz/decode-above" #[] (raw16 0xf45c), rng1)
    | 20 =>
        (mkCaseProgram
            "fuzz/gas/exact-miss"
            #[.null, intV 7, intV 8]
            #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instrIntSigned]
            gasExact, rng1)
    | _ =>
        (mkCaseProgram
        "fuzz/gas/exact-minus-one-miss"
            #[.null, intV 7, intV 8]
            #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instrIntSigned]
            gasExactMinusOne, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := dictDelId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let got := runDispatchFallback #[]
        match got with
        | .ok stack =>
            if stack != #[intV dispatchSentinel] then
              throw (IO.userError s!"dispatch fallback: expected sentinel stack, got {reprStr stack}")
        | .error e =>
            throw (IO.userError s!"dispatch fallback: expected ok, got error {e}") },
    { name := "unit/exec/signed-hit" -- [B2] [B3] [B7]
      run := do
        expectOkStack "signed-hit" (runSigned #[(.cell dictSliceSignedN8One), intV 7, intV 8]) #[.null, intV (-1)] },
    { name := "unit/exec/signed-miss" -- [B7]
      run := do
        expectOkStack "signed-miss" (runSigned #[(.cell dictSliceSignedN8One), intV 9, intV 8]) #[.cell dictSliceSignedN8One, intV 0] },
    { name := "unit/exec/signed-zero" -- [B7]
      run := do
        expectOkStack "signed-zero-hit" (runSigned #[(.cell dictSliceSignedN0One), intV 0, intV 0]) #[.null, intV (-1)] },
    { name := "unit/exec/unsigned-hit" -- [B7]
      run := do
        expectOkStack "unsigned-hit" (runUnsigned #[(.cell dictSliceUnsignedN8One), intV 7, intV 8]) #[.null, intV (-1)] },
    { name := "unit/exec/unsigned-miss" -- [B7]
      run := do
        expectOkStack "unsigned-miss" (runUnsigned #[(.cell dictSliceUnsignedN8One), intV 9, intV 8]) #[.cell dictSliceUnsignedN8One, intV 0] },
    { name := "unit/exec/unsigned-zero" -- [B7]
      run := do
        expectOkStack "unsigned-zero-hit" (runUnsigned #[(.cell dictSliceUnsignedN0One), intV 0, intV 0]) #[.null, intV (-1)] },
    { name := "unit/exec/slice-hit" -- [B7]
      run := do
        expectOkStack "slice-hit" (runSlice #[(.cell dictSliceSignedN8One), .slice key7Slice, intV 8]) #[.null, intV (-1)] },
    { name := "unit/exec/slice-miss" -- [B7]
      run := do
        expectOkStack "slice-miss" (runSlice #[(.cell dictSliceSignedN8One), .slice (mkSliceFromBits (natToBits 9 8)), intV 8]) #[.cell dictSliceSignedN8One, intV 0] },
    { name := "unit/exec/slice-underflow" -- [B6]
      run := do
        expectErr "slice-key-underflow" (runSlice #[(.cell dictSliceSignedN8One), .slice key3ShortSlice, intV 8]) .cellUnd },
    { name := "unit/exec/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runSigned #[]) .stkUnd },
    { name := "unit/exec/underflow-one-item" -- [B2]
      run := do
        expectErr "underflow-one-item" (runSigned #[.cell dictSliceSignedN8One]) .stkUnd },
    { name := "unit/err/n-nan" -- [B3]
      run := do
        expectErr "n-nan" (runSigned #[(.cell dictSliceSignedN8One), intV 7, .int .nan]) .rangeChk },
    { name := "unit/err/n-negative" -- [B3]
      run := do
        expectErr "n-negative" (runSigned #[(.cell dictSliceSignedN8One), intV 7, intV (-1)]) .rangeChk },
    { name := "unit/err/n-too-large" -- [B3]
      run := do
        expectErr "n-too-large" (runSigned #[(.cell dictSliceSignedN8One), intV 7, intV 2000]) .rangeChk },
    { name := "unit/err/key-type-signed" -- [B5]
      run := do
        expectErr "key-type-signed" (runSigned #[(.cell dictSliceSignedN8One), .slice key7Slice, intV 8]) .typeChk },
    { name := "unit/err/key-type-slice" -- [B5]
      run := do
        expectErr "key-type-slice" (runSlice #[(.cell dictSliceSignedN8One), intV 7, intV 8]) .typeChk },
    { name := "unit/err/dict-type-signed" -- [B4]
      run := do
        expectErr "dict-type-signed" (runSigned #[(.slice key7Slice), intV 7, intV 8]) .typeChk },
    { name := "unit/err/dict-type-slice" -- [B4]
      run := do
        expectErr "dict-type-slice" (runSlice #[.slice key7Slice, .slice key7Slice, intV 8]) .typeChk },
    { name := "unit/err/key-range-signed-high" -- [B5]
      run := do
        expectErr "key-range-signed-high" (runSigned #[(.cell dictSliceSignedN8One), intV 128, intV 8]) .rangeChk },
    { name := "unit/err/key-range-unsigned-negative" -- [B5]
      run := do
        expectErr "key-range-unsigned-negative" (runUnsigned #[(.cell dictSliceUnsignedN8One), intV (-1), intV 8]) .rangeChk },
    { name := "unit/err/key-range-unsigned-high" -- [B5]
      run := do
        expectErr "key-range-unsigned-high" (runUnsigned #[(.cell dictSliceUnsignedN8One), intV 256, intV 8]) .rangeChk },
    { name := "unit/decode/valid-opcodes" -- [B10]
      run := do
        let _ ← expectDecodeOk "decode-slice" instrSliceCode instrSlice
        let _ ← expectDecodeOk "decode-signed" instrIntSignedCode instrIntSigned
        let _ ← expectDecodeOk "decode-unsigned" instrIntUnsignedCode instrIntUnsigned },
    { name := "unit/decode/boundaries" -- [B10]
      run := do
        expectDecodeErr "decode-below-boundary" (raw16 0xf458) .invOpcode
        expectDecodeErr "decode-above-boundary" (raw16 0xf45c) .invOpcode
        match decodeCp0WithBits (Slice.ofCell (raw8 0xf4)) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode should reject truncated 8-bit opcode") },
    { name := "unit/asm/unsupported-slice" -- [B9]
      run := do
        expectAssembleErr "asm-slice" instrSlice .invOpcode },
    { name := "unit/asm/unsupported-signed" -- [B9]
      run := do
        expectAssembleErr "asm-signed" instrIntSigned .invOpcode },
    { name := "unit/asm/unsupported-unsigned" -- [B9]
      run := do
        expectAssembleErr "asm-unsigned" instrIntUnsigned .invOpcode }
  ]
  oracle := #[
    -- [B2]
    mkCaseSigned "oracle/underflow-empty" #[],
    -- [B2]
    mkCaseSigned "oracle/underflow-one-item" #[.cell dictSliceSignedN8One],
    -- [B3]
    mkCaseSigned "oracle/nan" #[.cell dictSliceSignedN8One, intV 7, .int .nan],
    -- [B3]
    mkCaseSigned "oracle/n-negative" #[.cell dictSliceSignedN8One, intV 7, intV (-1)],
    -- [B3]
    mkCaseSigned "oracle/n-too-large" #[.cell dictSliceSignedN8One, intV 7, intV 2000],
    -- [B3]
    mkCaseSigned "oracle/n-type" #[(.cell dictSliceSignedN8One), intV 7, .tuple #[]],
    mkCaseSigned "oracle/key-underflow" #[.cell dictSliceSignedN8One, .slice key3ShortSlice, intV 8],
    -- [B3/B4]
    mkCaseSigned "oracle/key-out-of-range-high" #[.cell dictSliceSignedN8One, intV 128, intV 8],
    -- [B3/B4]
    mkCaseSigned "oracle/key-out-of-range-low" #[.cell dictSliceSignedN8One, intV (-129), intV 8],
    -- [B4]
    mkCaseSlice "oracle/key-underflow-slice" #[.cell dictSliceSignedN8One, .slice key3ShortSlice, intV 8],
    -- [B4]
    mkCaseSigned "oracle/key-non-int-signed" #[(.cell dictSliceSignedN8One), .tuple #[], intV 8],
    -- [B4]
    mkCaseSlice "oracle/key-non-int-slice" #[.cell dictSliceSignedN8One, .tuple #[], intV 8] ,
    -- [B4]
    mkCaseSigned "oracle/dict-non-cell-signed" #[.tuple #[], intV 7, intV 8],
    -- [B4]
    mkCaseSlice "oracle/dict-non-cell-slice" #[.tuple #[], .slice key7Slice, intV 8],
    -- [B5]
    mkCaseSlice "oracle/signed-hit" #[(.cell dictSliceSignedN8One), .slice key7Slice, intV 8],
    -- [B5]
    mkCaseSlice "oracle/signed-miss" #[(.cell dictSliceSignedN8One), .slice (mkSliceFromBits (natToBits 9 8)), intV 8],
    -- [B5]
    mkCaseSigned "oracle/signed-hit-single" #[(.cell dictSliceSignedN8One), intV 7, intV 8],
    -- [B5]
    mkCaseSigned "oracle/signed-miss-single" #[(.cell dictSliceSignedN8One), intV 9, intV 8],
    -- [B5]
    mkCaseSigned "oracle/signed-hit-many" #[(.cell dictSliceSignedN8Many), intV 127, intV 8],
    -- [B5]
    mkCaseSigned "oracle/signed-non-match" #[(.cell dictSliceSignedN8Many), intV 1, intV 8],
    -- [B5]
    mkCaseSigned "oracle/signed-zero" #[(.cell dictSliceSignedN0One), intV 0, intV 0],
    -- [B5]
    mkCaseUnsigned "oracle/unsigned-hit" #[(.cell dictSliceUnsignedN8One), intV 7, intV 8],
    -- [B5]
    mkCaseUnsigned "oracle/unsigned-miss" #[(.cell dictSliceUnsignedN8One), intV 3, intV 8],
    -- [B5]
    mkCaseUnsigned "oracle/unsigned-hit-many" #[(.cell dictSliceUnsignedN8Many), intV 255, intV 8],
    -- [B5]
    mkCaseUnsigned "oracle/unsigned-miss-many" #[(.cell dictSliceUnsignedN8Many), intV 2, intV 8],
    -- [B5]
    mkCaseUnsigned "oracle/unsigned-zero" #[(.cell dictSliceUnsignedN0One), intV 0, intV 0],
    -- [B5]
    mkCaseUnsigned "oracle/unsigned-range-low" #[(.cell dictSliceUnsignedN8One), intV (-1), intV 8],
    -- [B5]
    mkCaseUnsigned "oracle/unsigned-range-high" #[(.cell dictSliceUnsignedN8One), intV 256, intV 8],
    -- [B8]
    mkCaseSigned "oracle/malformed-a" #[(.cell malformedDictA), intV 7, intV 8],
    -- [B8]
    mkCaseUnsigned "oracle/malformed-b" #[(.cell malformedDictB), intV 7, intV 8],
    -- [B10]
    mkCaseCode "oracle/decode/f459" #[] instrSliceCode,
    -- [B10]
    mkCaseCode "oracle/decode/f45a" #[] instrIntSignedCode,
    -- [B10]
    mkCaseCode "oracle/decode/f45b" #[] instrIntUnsignedCode,
    -- [B10]
    mkCaseCode "oracle/decode/below" #[] (raw16 0xf458),
    -- [B10]
    mkCaseCode "oracle/decode/above" #[] (raw16 0xf45c),
    -- [B10]
    mkCaseCode "oracle/decode/truncated-8" #[] (raw8 0xf4),
    -- [B11]
    mkCaseProgram "oracle/gas/exact-miss" (#[(.null), intV 7, intV 8])
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instrIntSigned]) gasExact,
    -- [B11]
    mkCaseProgram "oracle/gas/exact-minus-one-miss" #[(.null), intV 7, intV 8]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instrIntSigned]) gasExactMinusOne,
    -- [B11]
    mkCaseProgram "oracle/gas/hit-signed-exact" (#[(.cell dictSliceSignedN8Many), intV 127, intV 8])
      (#[.pushInt (.num hitSignedGas), .tonEnvOp .setGasLimit, instrIntSigned]) gasHitSignedExact,
    -- [B11]
    mkCaseProgram "oracle/gas/hit-signed-exact-minus-one" #[(.cell dictSliceSignedN8Many), intV 127, intV 8]
      (#[.pushInt (.num hitSignedGasMinusOne), .tonEnvOp .setGasLimit, instrIntSigned]) gasHitSignedMinusOne,
    -- [B11]
    mkCaseProgram "oracle/gas/hit-unsigned-exact" (#[(.cell dictSliceUnsignedN8Many), intV 255, intV 8])
      (#[.pushInt (.num hitUnsignedGas), .tonEnvOp .setGasLimit, instrIntUnsigned]) gasHitUnsignedExact,
    -- [B11]
    mkCaseProgram "oracle/gas/hit-unsigned-exact-minus-one" #[(.cell dictSliceUnsignedN8Many), intV 255, intV 8]
      (#[.pushInt (.num hitUnsignedGasMinusOne), .tonEnvOp .setGasLimit, instrIntUnsigned]) gasHitUnsignedMinusOne
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictDelId
      count := 500
      gen := genDICTIDEL
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIDEL
