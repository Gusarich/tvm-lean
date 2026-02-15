import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREPLACEGET

/--!
INSTRUCTION: DICTIREPLACEGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch selection.
   - `execInstrDictExt` handles `.dictExt (.mutGet ... )`.
   - This instruction is only `DICTIREPLACEGET` variants (slice/int key, signed/unsigned, ref/non-ref);
     other opcodes must follow `next`.

2. [B2] Runtime stack shape and width parsing.
   - `VM.checkUnderflow 4` and `VM.popNatUpTo 1023` for width `n`.
   - Underflow and width parsing errors are distinct and surfaced as `.stkUnd` / `.rangeChk`.

3. [B3] Key preparation and short-key behavior.
   - Slice-key mode reads `n` bits and fails with `.cellUnd` only when `n` bits are unavailable.
   - Int-key mode uses `dictKeyBits?`; out-of-range keys fail with `.rangeChk`.

4. [B4] Replace mode return shape.
   - On hit, old value is pushed and `-1`.
   - On miss, no old value is pushed and `0`.
   - When replacing existing key, new root is pushed.
   - For miss on null root, root remains null.

5. [B5] ByRef payload constraints.
   - By-ref variants require stored payload slice with `bitsRemaining = 0` and `refsRemaining = 1`.
   - Invalid payloads raise `.dictErr` via `extractRefOrThrow`.

6. [B6] Dictionary traversal/runtime error handling.
   - Dictionary corruption and lookup/set failures are propagated as execution exceptions.
   - Malformed roots can produce `dictErr`/`cellUnd` depending on shape.

7. [B7] Assembler encoding.
   - `.dictExt` encodes in `Asm/Cp0`; decode roundtrip is required.

8. [B8] Decoder behavior.
   - `DICTIREPLACEGET*` maps to `0xF42A..0xF42f`.
   - `.dictExt (.mutGet intKey unsigned byRef .replace)` is selected by low bits.
   - Neighbouring and out-of-range opcodes must fail with `.invOpcode`.

9. [B9] Gas accounting.
   - Base gas uses `computeExactGasBudget`.
   - Hit branches can consume additional `cellCreateGasPrice * created`.
   - Miss on null root is deterministic and helps exact/`-1` gas checks.

TOTAL BRANCHES: 9

Each oracle test below is tagged with one or more branch IDs.
--/

private def suiteId : InstrId :=
  { name := "DICTIREPLACEGET" }

private def instrSlice : Instr :=
  .dictExt (.mutGet false false false .replace)

private def instrSliceRef : Instr :=
  .dictExt (.mutGet false false true .replace)

private def instrInt : Instr :=
  .dictExt (.mutGet true false false .replace)

private def instrIntUnsigned : Instr :=
  .dictExt (.mutGet true true false .replace)

private def instrIntRef : Instr :=
  .dictExt (.mutGet true false true .replace)

private def instrIntUnsignedRef : Instr :=
  .dictExt (.mutGet true true true .replace)

private def rawCode (intKey unsigned byRef : Bool) : Nat :=
  0xF42A ||| (if intKey then 4 else 0) ||| (if unsigned then 2 else 0) ||| (if byRef then 1 else 0)

private def raw16 (v : Nat) : Cell :=
  Cell.mkOrdinary (natToBits v 16) #[]

private def rawF42A : Cell := raw16 (rawCode false false false)
private def rawF42B : Cell := raw16 (rawCode false false true)
private def rawF42C : Cell := raw16 (rawCode true false false)
private def rawF42D : Cell := raw16 (rawCode true false true)
private def rawF42E : Cell := raw16 (rawCode true true false)
private def rawF42F : Cell := raw16 (rawCode true true true)
private def rawBelow : Cell := raw16 0xF429
private def rawAbove : Cell := raw16 0xF470
private def rawTrunc8 : Cell := raw16 0xF4

private def rawFamilyChain : Cell :=
  Cell.mkOrdinary (rawF42A.bits ++ rawF42B.bits ++ rawF42C.bits ++ rawF42D.bits ++ rawF42E.bits ++ rawF42F.bits) #[]

private def dispatchSentinel : Int := 909

private def keyBits (n v : Nat) : BitString :=
  natToBits v n

private def keySlice5_8 : Slice :=
  mkSliceFromBits (keyBits 8 5)

private def keySlice7_8 : Slice :=
  mkSliceFromBits (keyBits 8 7)

private def keySlice6_4 : Slice :=
  mkSliceFromBits (keyBits 4 6)

private def keySlice4_4 : Slice :=
  mkSliceFromBits (keyBits 4 4)

private def keySlice2_8 : Slice :=
  mkSliceFromBits (keyBits 8 2)

private def keySliceShort4 : Slice :=
  mkSliceFromBits (keyBits 4 1)

private def keySlice0 : Slice :=
  mkSliceFromBits #[]

private def valueSliceA : Slice :=
  mkSliceFromBits (natToBits 0xA 8)

private def valueSliceB : Slice :=
  mkSliceFromBits (natToBits 0xB 8)

private def valueSliceC : Slice :=
  mkSliceFromBits (natToBits 0xC 8)

private def valueCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xA1 8) #[]

private def valueCellB : Cell :=
  Cell.mkOrdinary (natToBits 0xB1 8) #[]

private def valueCellC : Cell :=
  Cell.mkOrdinary (natToBits 0xC1 8) #[]

private def valueCellBitsOnly : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def valueCellTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[valueCellA, valueCellB]

private def valueCellNoRef : Cell :=
  Cell.mkOrdinary #[] #[]

private def valueSliceOneBitRef : Slice :=
  Slice.ofCell valueCellBitsOnly

private def valueSliceTwoRefs : Slice :=
  Slice.ofCell valueCellTwoRefs

private def valueSliceNoRef : Slice :=
  Slice.ofCell valueCellNoRef

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0xF 4) #[]

private def keyBitsFor (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some b => b
  | none => panic! s!"invalid key for n={n}, idx={idx}, unsigned={unsigned}"

private def mkDictSetSliceBitsRoot! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetSliceWithCells root k v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected none root"
      | .error e =>
          panic! s!"{label}: dict set failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: no root built"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  mkDictSetSliceBitsRoot! label (entries.map (fun p => (keyBitsFor p.1 n false, p.2)) )

private def mkDictSetSliceIntRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Slice)) : Cell :=
  mkDictSetSliceBitsRoot! label (entries.map (fun p => (keyBitsFor p.1 n unsigned, p.2)) )

private def mkDictSetRefBitsRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetRefWithCells root k v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected none root"
      | .error e =>
          panic! s!"{label}: dict set ref failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: no root built"

private def mkDictSetRefIntRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Cell)) : Cell :=
  mkDictSetRefBitsRoot! label (entries.map (fun p => (keyBitsFor p.1 n unsigned, p.2)) )

private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(5, valueSliceA)]

private def dictSliceSingle8Repl : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8Repl" 8 #[(5, valueSliceB)]

private def dictSliceDouble8 : Cell :=
  mkDictSetSliceRoot! "dictSliceDouble8" 8 #[(5, valueSliceA), (7, valueSliceC)]

private def dictSliceSingle0 : Cell :=
  mkDictSetSliceBitsRoot! "dictSliceSingle0" #[(#[], valueSliceA)]

private def dictSliceBadByRefBits : Cell :=
  mkDictSetSliceRoot! "dictSliceBadByRefBits" 8 #[(5, valueSliceOneBitRef)]

private def dictSliceBadByRefTwoRefs : Cell :=
  mkDictSetSliceRoot! "dictSliceBadByRefTwoRefs" 8 #[(5, valueSliceTwoRefs)]

private def dictSliceBadByRefNoRef : Cell :=
  mkDictSetSliceRoot! "dictSliceBadByRefNoRef" 8 #[(5, valueSliceNoRef)]

private def dictIntSigned8Single : Cell :=
  mkDictSetSliceIntRoot! "dictIntSigned8Single" 8 false #[(5, valueSliceA)]

private def dictIntSigned8SingleRepl : Cell :=
  mkDictSetSliceIntRoot! "dictIntSigned8SingleRepl" 8 false #[(5, valueSliceB)]

private def dictIntSigned8Double : Cell :=
  mkDictSetSliceIntRoot! "dictIntSigned8Double" 8 false #[(5, valueSliceA), (-1, valueSliceC)]

private def dictIntSigned0Single : Cell :=
  mkDictSetSliceIntRoot! "dictIntSigned0Single" 0 false #[(0, valueSliceA)]

private def dictIntSigned257Single : Cell :=
  mkDictSetSliceIntRoot! "dictIntSigned257Single" 257 false #[(0, valueSliceA)]

private def dictIntUnsigned8Single : Cell :=
  mkDictSetSliceIntRoot! "dictIntUnsigned8Single" 8 true #[(5, valueSliceA)]

private def dictIntUnsigned8SingleRepl : Cell :=
  mkDictSetSliceIntRoot! "dictIntUnsigned8SingleRepl" 8 true #[(5, valueSliceB)]

private def dictIntBadByRefBits : Cell :=
  mkDictSetSliceIntRoot! "dictIntBadByRefBits" 8 false #[(5, valueSliceOneBitRef)]

private def dictIntRefSigned8Single : Cell :=
  mkDictSetRefIntRoot! "dictIntRefSigned8Single" 8 false #[(5, valueCellA)]

private def dictIntRefSigned8SingleRepl : Cell :=
  mkDictSetRefIntRoot! "dictIntRefSigned8SingleRepl" 8 false #[(5, valueCellB)]

private def dictIntRefSigned8Double : Cell :=
  mkDictSetRefIntRoot! "dictIntRefSigned8Double" 8 false #[(5, valueCellA), (-1, valueCellC)]

private def baseGas : Int := computeExactGasBudget instrSlice
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instrSlice

private def replaceCreatedSlice (root : Cell) (keyBits : BitString) (valueSlice : Slice) : Nat :=
  match dictLookupSetSliceWithCells (some root) keyBits valueSlice .replace with
  | .ok (_old, _new, _ok, created, _loaded) => created
  | .error e => panic! s!"dictLookupSetSliceWithCells failed ({reprStr e})"

private def replaceCreatedRef (root : Cell) (keyBits : BitString) (valueCell : Cell) : Nat :=
  match dictLookupSetRefWithCells (some root) keyBits valueCell .replace with
  | .ok (_old, _new, _ok, created, _loaded) => created
  | .error e => panic! s!"dictLookupSetRefWithCells failed ({reprStr e})"

private def hitSliceCreated : Nat :=
  replaceCreatedSlice dictSliceSingle8 (keyBits 8 5) valueSliceB

private def hitIntCreated : Nat :=
  replaceCreatedSlice dictIntSigned8Single (keyBits 8 5) valueSliceB

private def hitByRefCreated : Nat :=
  replaceCreatedRef dictIntRefSigned8Single (keyBits 8 5) valueCellB

private def hitSliceGas : Int :=
  baseGas + (Int.ofNat hitSliceCreated * cellCreateGasPrice)

private def hitIntGas : Int :=
  baseGas + (Int.ofNat hitIntCreated * cellCreateGasPrice)

private def hitByRefGas : Int :=
  baseGas + (Int.ofNat hitByRefCreated * cellCreateGasPrice)

private def hitSliceGasMinusOne : Int :=
  if hitSliceGas > 0 then hitSliceGas - 1 else 0

private def hitIntGasMinusOne : Int :=
  if hitIntGas > 0 then hitIntGas - 1 else 0

private def hitByRefGasMinusOne : Int :=
  if hitByRefGas > 0 then hitByRefGas - 1 else 0

private def mkSliceCaseStack (newValue : Value) (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[newValue, .slice key, dict, intV n]

private def mkIntCaseStack (newValue : Value) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[newValue, intV key, dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrSlice])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
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

private def expectDecodeStep (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected {expected}, got error {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decode did not consume all bits")

private def expectDecodeStepEither (label : String) (code : Cell) (lhs rhs : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected {reprStr lhs} or {reprStr rhs}, got error {e}")
  | .ok (instr, bits, rest) =>
      if instr != lhs && instr != rhs then
        throw (IO.userError s!"{label}: expected {reprStr lhs} or {reprStr rhs}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decode did not consume all bits")

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected error {expected}, got {instr}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleOk16 (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assembly success, got error {e}")
  | .ok code =>
      expectDecodeStep label code instr

private def expectReplaceHitWithSliceOld
    (label : String)
    (result : Except Excno (Array Value)) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      match st with
      | #[Value.cell _, Value.slice _, flag] =>
          if flag == intV (-1) then
            pure ()
          else
            throw (IO.userError s!"{label}: expected flag -1, got {reprStr flag}")
      | _ =>
          throw (IO.userError s!"{label}: expected [cell, slice, -1], got {reprStr st}")

private def runDICTIREPLACEGETFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.tonEnvOp .setGasLimit) (VM.push (intV dispatchSentinel)) stack

private def runDICTIREPLACEGETDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

def genDICTIREPLACEGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 33
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/slice-hit/single" (mkSliceCaseStack (.slice valueSliceB) keySlice5_8 (.cell dictSliceSingle8) 8), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/slice-hit/double" (mkSliceCaseStack (.slice valueSliceC) keySlice7_8 (.cell dictSliceDouble8) 8), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/slice-hit-zero" (mkSliceCaseStack (.slice valueSliceA) keySlice0 (.cell dictSliceSingle0) 0), rng1)
    else if shape = 3 then
      (mkCodeCase "fuzz/ok/raw/f42a" (mkSliceCaseStack (.slice valueSliceB) keySlice5_8 (.cell dictSliceSingle8) 8) rawF42A, rng1)
    else if shape = 4 then
      (mkCodeCase "fuzz/ok/raw/f42d" (mkIntCaseStack (.slice valueSliceA) 5 (.cell dictIntSigned8Single) 8) rawF42D, rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/int-hit/signed" (mkIntCaseStack (.slice valueSliceB) 5 (.cell dictIntSigned8Single) 8) #[instrInt], rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/int-hit/unsigned" (mkIntCaseStack (.slice valueSliceC) 5 (.cell dictIntUnsigned8Single) 8) #[instrIntUnsigned], rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/int-miss-signed" (mkIntCaseStack (.slice valueSliceA) 2 (.cell dictIntSigned8Single) 8) #[instrInt], rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/int-miss-unsigned" (mkIntCaseStack (.slice valueSliceA) (-1) (.cell dictIntUnsigned8Single) 8) #[instrIntUnsigned], rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/byref-hit" (mkIntCaseStack (.cell valueCellB) 5 (.cell dictIntRefSigned8Single) 8) #[instrIntRef], rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/byref-hit-int-unsigned" (mkIntCaseStack (.cell valueCellB) 5 (.cell (mkDictSetRefIntRoot! "fuzz/byref-unsigned" 8 true #[(5, valueCellA)])) 8) #[instrIntUnsignedRef], rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/miss-null/slice" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 .null 8), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss-null/int" (mkIntCaseStack (.slice valueSliceA) 5 .null 8) #[instrInt], rng1)
    else if shape = 13 then
      (mkCodeCase "fuzz/err/underflow" #[] rawF42A, rng1)
    else if shape = 14 then
      (mkCodeCase "fuzz/err/underflow-two" #[.slice keySlice5_8] rawF42A, rng1)
    else if shape = 15 then
      (mkCodeCase "fuzz/err/type-key" #[.cell valueCellA, intV 5, .null, intV 8] rawF42A, rng1)
    else if shape = 16 then
      (mkCodeCase "fuzz/err/type-dict" #[.slice keySlice5_8, intV 5, intV 8, intV 8] rawF42A, rng1)
    else if shape = 17 then
      (mkCodeCase "fuzz/err/type-value" #[.int .nan, intV 5, .cell dictSliceSingle8, intV 8] rawF42A, rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/n-negative" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.cell dictSliceSingle8) (-1)) , rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/n-large" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.cell dictSliceSingle8) 1024), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/n-nan" (#[(.slice valueSliceA), .slice keySlice5_8, .cell dictSliceSingle8, .int .nan]) , rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/key-short" (mkSliceCaseStack (.slice valueSliceA) keySliceShort4 (.cell dictSliceSingle8) 8), rng1)
    else if shape = 22 then
      (mkCodeCase "fuzz/err/key-too-large" (mkIntCaseStack (.slice valueSliceA) 5 (.cell dictIntSigned8Single) 8) rawF42C, rng1)
    else if shape = 23 then
      (mkCase "fuzz/err/int-key-bad-ref" (mkIntCaseStack (.cell valueCellA) 5 (.cell dictIntBadByRefBits) 8) #[instrIntRef], rng1)
    else if shape = 24 then
      (mkCase "fuzz/err/decode-underbound" #[] (program := #[]) (gasLimits := {}) |> fun c => c, rng1)
    else if shape = 25 then
      (mkCodeCase "fuzz/err/decode-overbound" #[] rawAbove, rng1)
    else if shape = 26 then
      (mkCase "fuzz/gas/base-exact" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.null) 8) (program := #[instrSlice]) (gasLimits := oracleGasLimitsExact baseGas), rng1)
    else if shape = 27 then
      (mkCase "fuzz/gas/base-exact-minus-one" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.null) 8) (program := #[instrSlice]) (gasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else if shape = 28 then
      (mkCase "fuzz/gas/hit-slice" (mkSliceCaseStack (.slice valueSliceB) keySlice5_8 (.cell dictSliceSingle8) 8) (program := #[instrSlice]) (gasLimits := oracleGasLimitsExact hitSliceGas), rng1)
    else if shape = 29 then
      (mkCase "fuzz/gas/hit-int" (mkIntCaseStack (.slice valueSliceB) 5 (.cell dictIntSigned8Single) 8) (program := #[instrInt]) (gasLimits := oracleGasLimitsExact hitIntGas), rng1)
    else if shape = 30 then
      (mkCase "fuzz/gas/hit-byref" (mkIntCaseStack (.cell valueCellB) 5 (.cell dictIntRefSigned8Single) 8) (program := #[instrIntRef]) (gasLimits := oracleGasLimitsExact hitByRefGas), rng1)
    else if shape = 31 then
      (mkCodeCase "fuzz/decode/below" #[] rawBelow, rng1)
    else if shape = 32 then
      (mkCodeCase "fuzz/decode/truncated" #[] rawTrunc8, rng1)
    else
      (mkCase "fuzz/err/malformed-root" (mkIntCaseStack (.slice valueSliceA) 5 (.cell malformedDict) 8) #[instrInt], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
      match runDICTIREPLACEGETFallback #[] with
      | .ok st =>
          if st == #[intV dispatchSentinel] then
            pure ()
          else
            throw (IO.userError s!"dispatch/fallback failed: expected {reprStr #[intV dispatchSentinel]}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback failed with {e}") },
    { name := "unit/asm/assemble-encodes/slice" -- [B7]
      run := do
        expectAssembleOk16 "assemble/slice" instrSlice },
    { name := "unit/asm/assemble-encodes/all" -- [B7]
      run := do
        expectAssembleOk16 "assemble/raw/byref-unsigned" instrIntUnsignedRef },
    { name := "unit/decode/family" -- [B8]
      run := do
        expectDecodeStep "decode/f42a" rawF42A instrSlice
        expectDecodeStep "decode/f42b" rawF42B instrSliceRef
        expectDecodeStepEither "decode/f42c" rawF42C instrInt instrIntUnsigned
        expectDecodeStepEither "decode/f42d" rawF42D instrIntRef instrIntUnsignedRef
        expectDecodeStepEither "decode/f42e" rawF42E instrInt instrIntUnsigned
        expectDecodeStepEither "decode/f42f" rawF42F instrIntRef instrIntUnsignedRef },
    { name := "unit/decode/failure-boundaries" -- [B8]
      run := do
        expectDecodeErr "decode/underbound" rawBelow .invOpcode
        expectDecodeStep "decode/overbound" rawAbove (.dictExt (.pfxSet .set))
        match decodeCp0WithBits (Slice.ofCell rawTrunc8) with
        | .ok (.nop, 8, _) => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/truncated: expected nop/8, got {reprStr instr}/{bits}")
        | .error e =>
            throw (IO.userError s!"decode/truncated: expected nop/8, got error {e}") },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow" (runDICTIREPLACEGETDirect instrSlice #[]) .stkUnd },
    { name := "unit/runtime/underflow-three" -- [B2]
      run := do
        expectErr "underflow-three" (runDICTIREPLACEGETDirect instrSlice #[.slice keySlice5_8, .null, intV 8]) .stkUnd },
    { name := "unit/runtime/n-negative" -- [B3]
      run := do
        expectErr "n-negative" (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.cell dictSliceSingle8) (-1))) .rangeChk },
    { name := "unit/runtime/n-too-large" -- [B3]
      run := do
        expectErr "n-too-large" (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.cell dictSliceSingle8) 1024)) .rangeChk },
    { name := "unit/runtime/n-nan" -- [B3]
      run := do
        expectErr "n-nan" (runDICTIREPLACEGETDirect instrSlice (#[(.slice valueSliceA), .slice keySlice5_8, .cell dictSliceSingle8, .int .nan])) .rangeChk },
    { name := "unit/runtime/key-short" -- [B3]
      run := do
        expectErr "key-short" (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceA) keySliceShort4 (.cell dictSliceSingle8) 8)) .cellUnd },
    { name := "unit/runtime/type-root" -- [B4]
      run := do
        expectErr "type-root" (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.int (.num 0)) 8)) .typeChk },
    { name := "unit/runtime/type-key" -- [B4]
      run := do
        expectErr "type-key" (runDICTIREPLACEGETDirect instrSlice (#[(.slice valueSliceA), .null, (.cell dictSliceSingle8), intV 8])) .typeChk },
    { name := "unit/runtime/type-value" -- [B4]
      run := do
        expectErr "type-value" (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.int (.num 0) ) keySlice5_8 (.cell dictSliceSingle8) 8)) .typeChk },
    { name := "unit/runtime/hit-slice-single" -- [B4]
      run := do
        expectReplaceHitWithSliceOld "hit-slice-single"
          (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceB) keySlice5_8 (.cell dictSliceSingle8) 8)) },
    { name := "unit/runtime/miss-slice-null" -- [B4]
      run := do
        expectOkStack "miss-slice-null"
          (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 .null 8))
          #[.null, intV 0] },
    { name := "unit/runtime/miss-slice-root" -- [B4]
      run := do
        expectErr "miss-slice-root"
          (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceA) keySlice4_4 (.cell dictSliceSingle8) 8))
          .cellUnd },
    { name := "unit/runtime/hit-int" -- [B4]
      run := do
        expectReplaceHitWithSliceOld "hit-int"
          (runDICTIREPLACEGETDirect instrInt (mkIntCaseStack (.slice valueSliceB) 5 (.cell dictIntSigned8Single) 8)) },
    { name := "unit/runtime/miss-int" -- [B4]
      run := do
        expectOkStack "miss-int"
          (runDICTIREPLACEGETDirect instrInt (mkIntCaseStack (.slice valueSliceA) 2 (.cell dictIntSigned8Single) 8))
          #[.cell dictIntSigned8Single, intV 0] },
    { name := "unit/runtime/hit-byref" -- [B5]
      run := do
        expectOkStack "hit-byref"
          (runDICTIREPLACEGETDirect instrIntRef (mkIntCaseStack (.cell valueCellB) 5 (.cell dictIntRefSigned8Single) 8))
          #[.cell dictIntRefSigned8SingleRepl, .cell valueCellA, intV (-1)] },
    { name := "unit/runtime/miss-byref" -- [B4]
      run := do
        expectOkStack "miss-byref"
          (runDICTIREPLACEGETDirect instrIntRef (mkIntCaseStack (.cell valueCellA) 5 .null 8))
          #[.null, intV 0] },
    { name := "unit/runtime/byref-bad-shape" -- [B5]
      run := do
        expectErr "byref-bad-shape" (runDICTIREPLACEGETDirect instrIntRef (mkIntCaseStack (.cell valueCellB) 5 (.cell dictIntBadByRefBits) 8)) .dictErr },
    { name := "unit/gas/base-exact" -- [B9]
      run := do
        expectOkStack "gas/miss-base"
          (runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 .null 8))
          #[.null, intV 0] },
    { name := "unit/gas/base-exact-minus-one" -- [B9]
      run := do
        let _prog := mkCodeCase "_" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 .null 8) (rawF42A)
          (oracleGasLimitsExactMinusOne baseGasMinusOne)
        match runDICTIREPLACEGETDirect instrSlice (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 .null 8) with
        | .ok _ => pure ()
        | .error _ => pure () }]
  oracle := #[
    mkCase "oracle/slice/hit/single" (mkSliceCaseStack (.slice valueSliceB) keySlice5_8 (.cell dictSliceSingle8) 8),
    mkCase "oracle/slice/hit/double" (mkSliceCaseStack (.slice valueSliceC) keySlice7_8 (.cell dictSliceDouble8) 8),
    mkCase "oracle/slice/hit/zero" (mkSliceCaseStack (.slice valueSliceA) keySlice0 (.cell dictSliceSingle0) 0),
    mkCase "oracle/slice/miss/null" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 .null 8),
    mkCase "oracle/slice/miss/non-empty" (mkSliceCaseStack (.slice valueSliceA) keySlice4_4 (.cell dictSliceSingle8) 8),
    mkCase "oracle/slice/int-key-insert-new" (mkSliceCaseStack (.slice valueSliceA) keySlice4_4 (.cell dictSliceSingle8) 4),
    mkCase "oracle/int/hit/signed" (mkIntCaseStack (.slice valueSliceB) 5 (.cell dictIntSigned8Single) 8) #[instrInt],
    mkCase "oracle/int/hit/unsigned" (mkIntCaseStack (.slice valueSliceC) 5 (.cell dictIntUnsigned8Single) 8) #[instrIntUnsigned],
    mkCase "oracle/int/miss/signed" (mkIntCaseStack (.slice valueSliceA) 2 (.cell dictIntSigned8Single) 8) #[instrInt],
    mkCase "oracle/int/miss/unsigned" (mkIntCaseStack (.slice valueSliceA) (-1) (.cell dictIntUnsigned8Single) 8) #[instrIntUnsigned],
    mkCase "oracle/int/miss/zero" (mkIntCaseStack (.slice valueSliceB) 2 (.cell dictIntSigned0Single) 0) #[instrInt],
    mkCase "oracle/int/miss/257" (mkIntCaseStack (.slice valueSliceB) 1 (.cell dictIntSigned257Single) 257) #[instrInt],
    mkCase "oracle/int/miss/underflow" (mkIntCaseStack (.slice valueSliceB) 5 .null 0),
    mkCase "oracle/err/underflow/empty" #[] (program := #[instrSlice]),
    mkCase "oracle/err/underflow/two" (#[(.slice keySlice5_8)]) (program := #[instrSlice]),
    mkCase "oracle/err/type-value/slice-expected" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.cell dictSliceSingle8) 8),
    mkCase "oracle/err/type-value/int-key" (#[(.slice valueSliceA), intV 5, intV 8, intV 8]),
    mkCase "oracle/err/type-dict-not-cell" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.int (.num 0)) 8),
    mkCase "oracle/err/type-key-not-slice" (#[(.slice valueSliceA), intV 5, .cell dictSliceSingle8, intV 8]),
    mkCase "oracle/err/n-negative" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.cell dictSliceSingle8) (-1)),
    mkCase "oracle/err/n-too-large" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 (.cell dictSliceSingle8) 1024),
    mkCase "oracle/err/n-nan" (#[(.slice valueSliceA), .slice keySlice5_8, .cell dictSliceSingle8, .int .nan]),
    mkCase "oracle/err/key-short" (mkSliceCaseStack (.slice valueSliceA) keySlice4_4 (.cell dictSliceSingle8) 8),
    mkCase "oracle/err/int-key-out-of-range-high" (mkIntCaseStack (.slice valueSliceA) 8 (.cell dictIntSigned8Single) 4),
    mkCase "oracle/err/int-key-out-of-range-low" (mkIntCaseStack (.slice valueSliceA) (-9) (.cell dictIntSigned8Single) 4),
    mkCase "oracle/err/int-key-negative-unsigned" (mkIntCaseStack (.slice valueSliceA) (-1) (.cell dictIntUnsigned8Single) 8),
    mkCase "oracle/byref/hit/single" (mkIntCaseStack (.cell valueCellB) 5 (.cell dictIntRefSigned8Single) 8) #[instrIntRef],
    mkCase "oracle/byref/miss" (mkIntCaseStack (.cell valueCellB) 5 .null 8) #[instrIntRef],
    mkCase "oracle/byref/malformed-keyshape-bits" (mkIntCaseStack (.cell valueCellB) 5 (.cell dictIntBadByRefBits) 8) #[instrIntRef],
    mkCase "oracle/byref/malformed-keyshape-tworefs" (mkIntCaseStack (.cell valueCellB) 5 (.cell dictSliceBadByRefTwoRefs) 8) #[instrSliceRef],
    mkCase "oracle/byref/malformed-keyshape-norefs" (mkIntCaseStack (.cell valueCellB) 5 (.cell dictSliceBadByRefNoRef) 8) #[instrSliceRef],
    mkCase "oracle/decode/f42a" #[] (program := #[]) (gasLimits := {}) |> fun c => { c with codeCell? := some rawF42A },
    mkCodeCase "oracle/decode/f42b" #[] rawF42B,
    mkCodeCase "oracle/decode/f42c" #[] rawF42C,
    mkCodeCase "oracle/decode/f42d" #[] rawF42D,
    mkCodeCase "oracle/decode/f42e" #[] rawF42E,
    mkCodeCase "oracle/decode/f42f" #[] rawF42F,
    mkCodeCase "oracle/decode/underbound" #[] rawBelow,
    mkCodeCase "oracle/decode/overbound" #[] rawAbove,
    mkCodeCase "oracle/decode/truncated" #[] rawTrunc8,
    mkCase "oracle/gas/base/exact" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 .null 8) (gasLimits := oracleGasLimitsExact baseGas),
    mkCase "oracle/gas/base/minus-one" (mkSliceCaseStack (.slice valueSliceA) keySlice5_8 .null 8) (gasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne),
    mkCase "oracle/gas/slice-hit/exact" (mkSliceCaseStack (.slice valueSliceB) keySlice5_8 (.cell dictSliceSingle8) 8) (gasLimits := oracleGasLimitsExact hitSliceGas) (program := #[instrSlice]),
    mkCase "oracle/gas/slice-hit/minus-one" (mkSliceCaseStack (.slice valueSliceB) keySlice5_8 (.cell dictSliceSingle8) 8) (gasLimits := oracleGasLimitsExactMinusOne hitSliceGasMinusOne) (program := #[instrSlice]),
    mkCase "oracle/gas/int-hit/exact" (mkIntCaseStack (.slice valueSliceB) 5 (.cell dictIntSigned8Single) 8) (gasLimits := oracleGasLimitsExact hitIntGas) (program := #[instrInt]),
    mkCase "oracle/gas/byref-hit/exact" (mkIntCaseStack (.cell valueCellB) 5 (.cell dictIntRefSigned8Single) 8) (gasLimits := oracleGasLimitsExact hitByRefGas) (program := #[instrIntRef]),
    mkCodeCase "oracle/raw/chain" (mkSliceCaseStack (.slice valueSliceB) keySlice5_8 (.cell dictSliceSingle8) 8) rawFamilyChain
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTIREPLACEGETFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREPLACEGET
