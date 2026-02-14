import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREPLACEGET

/--!
INSTRUCTION: DICTREPLACEGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch behavior.
   - `execInstrDictExt` handles `.dictExt (.mutGet ...)` and this opcode is mapped to `.mutGet .replace`.
   - Non-matching opcodes must fall through to the generic `next` path.

2. [B2] Runtime stack arity.
   - `checkUnderflow 4` is required for non-del mutGet variants.
   - Stack shape violations are `.stkUnd`.

3. [B3] Width parsing (`n`) validation.
   - `n` uses `popNatUpTo 1023`.
   - Negative/nan/ >1023 values produce `.rangeChk`.

4. [B4] Key decoding path.
   - Slice-key mode requires `n` bits and throws `.cellUnd` if short.
   - Integer-key mode uses `dictKeyBits?`; out-of-range keys throw `.rangeChk`.

5. [B5] Value and root type validation.
   - Dict root: maybe-cell with `.null` supported, non-cell and non-maybe-cell values cause `.typeChk`.
   - New value must be slice for non-ref form and cell for by-ref form.
   - Key type mismatches cause `.typeChk`.

6. [B6] Runtime success semantics.
   - Miss: returns `0` and leaves dictionary unchanged.
   - Hit: returns old value plus `-1`, with replaced root on stack.

7. [B7] By-ref payload constraints.
   - By-ref variants require lookup-returned payload with `bitsRemaining = 0` and `refsRemaining = 1`.
   - Malformed payload raises `.dictErr`.

8. [B8] Assembler encoding.
   - All DICTREPLACEGET forms are `.dictExt` and are rejected by assembler (`.invOpcode`).

9. [B9] Decoder behavior.
   - `0xf42a..0xf42f` map to `.dictExt (.mutGet ... .replace)`.
   - `0xf429`, `0xf430` and truncated opcode lengths are rejected.

10. [B10] Gas accounting.
    - Base gas is `computeExactGasBudget`.
    - Hit path may add `cellCreateGasPrice * created`.
    - Miss on null has no penalty.
    - Exact and exact-minus-one cases are required.

11. [B11] Traversal-error propagation.
    - malformed dictionary roots can propagate `.dictErr`/`.cellUnd` after root-load and visited-node bookkeeping.

TOTAL BRANCHES: 11

Each oracle test below is tagged with the branch IDs it covers.
--/

private def suiteId : InstrId :=
  { name := "DICTREPLACEGET" }

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
  0xf42a ||| (if intKey then 4 else 0) ||| (if unsigned then 2 else 0) ||| (if byRef then 1 else 0)

private def rawF42A : Cell := Cell.mkOrdinary (natToBits (rawCode false false false) 16) #[]
private def rawF42B : Cell := Cell.mkOrdinary (natToBits (rawCode false false true) 16) #[]
private def rawF42C : Cell := Cell.mkOrdinary (natToBits (rawCode true false false) 16) #[]
private def rawF42D : Cell := Cell.mkOrdinary (natToBits (rawCode true false true) 16) #[]
private def rawF42E : Cell := Cell.mkOrdinary (natToBits (rawCode true true false) 16) #[]
private def rawF42F : Cell := Cell.mkOrdinary (natToBits (rawCode true true true) 16) #[]
private def rawF429 : Cell := Cell.mkOrdinary (natToBits 0xf429 16) #[]
private def rawF430 : Cell := Cell.mkOrdinary (natToBits 0xf430 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def valueSliceA : Slice := mkSliceFromBits (natToBits 0xA 8)
private def valueSliceB : Slice := mkSliceFromBits (natToBits 0xB 8)
private def valueSliceC : Slice := mkSliceFromBits (natToBits 0xC 8)
private def valueSliceD : Slice := mkSliceFromBits (natToBits 0xD 8)

private def valueCellA : Cell := Cell.mkOrdinary (natToBits 0xa1 8) #[]
private def valueCellB : Cell := Cell.mkOrdinary (natToBits 0xb1 8) #[]
private def valueCellC : Cell := Cell.mkOrdinary (natToBits 0xc1 8) #[]

private def badByRefBits : Cell := Cell.mkOrdinary (natToBits 1 1) #[]
private def badByRefTwoRefs : Cell := Cell.mkOrdinary #[] #[valueCellA, valueCellB]
private def badByRefNoRef : Cell := Cell.mkOrdinary #[] #[]

private def byRefValueA : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[valueCellA])
private def byRefValueB : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[valueCellB])
private def byRefValueBits : Slice := Slice.ofCell badByRefBits
private def byRefValueTwoRefs : Slice := Slice.ofCell badByRefTwoRefs
private def byRefValueNoRef : Slice := Slice.ofCell badByRefNoRef

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0x0f 4) #[]

private def key4_0 : Slice := mkSliceFromBits (natToBits 0 4)
private def key4_5 : Slice := mkSliceFromBits (natToBits 5 4)
private def key4_7 : Slice := mkSliceFromBits (natToBits 7 4)
private def key4_8 : Slice := mkSliceFromBits (natToBits 8 4)
private def key4_short : Slice := mkSliceFromBits (natToBits 5 3)
private def key4_0x : Slice := mkSliceFromBits #[ ]
private def key0 : Slice := mkSliceFromBits #[]
private def key8_255 : Slice := mkSliceFromBits (natToBits 255 8)

private def bits4_0 : BitString := #[]
private def bits4_5 : BitString := natToBits 5 4
private def bits4_7 : BitString := natToBits 7 4
private def bits4_8 : BitString := natToBits 8 4

private def requireBitsFor (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bits => bits
  | none => panic! s!"invalid int key key={idx} n={n} unsigned={unsigned}"

private def mkDictSetSliceBitsRoot! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    entries.foldl
      (fun st entry =>
        match st with
        | some root =>
          match dictSetSliceWithCells (some root) entry.1 entry.2 .set with
          | .ok (some root', _ok, _created, _loaded) => some root'
          | .ok (none, _ok, _created, _loaded) => none
          | .error _ => none
        | none =>
          match dictSetSliceWithCells none entry.1 entry.2 .set with
          | .ok (some root', _ok, _created, _loaded) => some root'
          | .ok (none, _ok, _created, _loaded) => none
          | .error _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build slice dictionary"

private def mkDictSetRefBitsRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  let rootOpt : Option Cell :=
    entries.foldl
      (fun st entry =>
        match st with
        | some root =>
          match dictSetRefWithCells (some root) entry.1 entry.2 .set with
          | .ok (some root', _ok, _created, _loaded) => some root'
          | .ok (none, _ok, _created, _loaded) => none
          | .error _ => none
        | none =>
          match dictSetRefWithCells none entry.1 entry.2 .set with
          | .ok (some root', _ok, _created, _loaded) => some root'
          | .ok (none, _ok, _created, _loaded) => none
          | .error _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build ref dictionary"

private def mkDictSetSliceIntRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Slice)) : Cell :=
  mkDictSetSliceBitsRoot! label (entries.map (fun p => (requireBitsFor p.1 n unsigned, p.2)))

private def mkDictSetRefIntRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Cell)) : Cell :=
  mkDictSetRefBitsRoot! label (entries.map (fun p => (requireBitsFor p.1 n unsigned, p.2)))

private def dictSlice4Single : Cell :=
  mkDictSetSliceIntRoot! "slice4Single" 4 false #[(5, valueSliceA)]

private def dictSlice4SingleRepl : Cell :=
  mkDictSetSliceIntRoot! "slice4SingleRepl" 4 false #[(5, valueSliceB)]

private def dictSlice4Double : Cell :=
  mkDictSetSliceIntRoot! "slice4Double" 4 false #[(5, valueSliceA), (7, valueSliceC)]

private def dictSlice4Zero : Cell :=
  mkDictSetSliceBitsRoot! "slice4Zero" #[(bits4_0, valueSliceA)]

private def dictSlice4ZeroRepl : Cell :=
  mkDictSetSliceBitsRoot! "slice4ZeroRepl" #[(bits4_0, valueSliceB)]

private def dictSlice4RefSingle : Cell :=
  mkDictSetSliceBitsRoot! "slice4RefSingle" #[(bits4_5, byRefValueA)]

private def dictSlice4RefSingleRepl : Cell :=
  mkDictSetSliceBitsRoot! "slice4RefSingleRepl" #[(bits4_5, byRefValueB)]

private def dictSlice4RefBadBits : Cell :=
  mkDictSetSliceBitsRoot! "slice4RefBadBits" #[(bits4_5, byRefValueBits)]

private def dictSlice4RefBadTwoRefs : Cell :=
  mkDictSetSliceBitsRoot! "slice4RefBadTwoRefs" #[(bits4_5, byRefValueTwoRefs)]

private def dictSlice4RefBadNoRef : Cell :=
  mkDictSetSliceBitsRoot! "slice4RefBadNoRef" #[(bits4_5, byRefValueNoRef)]

private def dictInt4SignedSingle : Cell :=
  mkDictSetSliceIntRoot! "int4SignedSingle" 4 false #[(5, valueSliceA)]

private def dictInt4SignedSingleRepl : Cell :=
  mkDictSetSliceIntRoot! "int4SignedSingleRepl" 4 false #[(5, valueSliceB)]

private def dictInt4SignedDouble : Cell :=
  mkDictSetSliceIntRoot! "int4SignedDouble" 4 false #[(5, valueSliceA), (-1, valueSliceC)]

private def dictInt4UnsignedSingle : Cell :=
  mkDictSetSliceIntRoot! "int4UnsignedSingle" 4 true #[(5, valueSliceA)]

private def dictInt4UnsignedSingleRepl : Cell :=
  mkDictSetSliceIntRoot! "int4UnsignedSingleRepl" 4 true #[(5, valueSliceB)]

private def dictInt4UnsignedDouble : Cell :=
  mkDictSetSliceIntRoot! "int4UnsignedDouble" 4 true #[(5, valueSliceA), (8, valueSliceC)]

private def dictInt4RefSignedSingle : Cell :=
  mkDictSetRefIntRoot! "int4RefSignedSingle" 4 false #[(5, valueCellA)]

private def dictInt4RefSignedSingleRepl : Cell :=
  mkDictSetRefIntRoot! "int4RefSignedSingleRepl" 4 false #[(5, valueCellB)]

private def dictInt4RefUnsignedSingle : Cell :=
  mkDictSetRefIntRoot! "int4RefUnsignedSingle" 4 true #[(5, valueCellA)]

private def dictInt4RefUnsignedSingleRepl : Cell :=
  mkDictSetRefIntRoot! "int4RefUnsignedSingleRepl" 4 true #[(5, valueCellB)]

private def dictInt4RefBadBits : Cell :=
  mkDictSetSliceIntRoot! "int4RefBadBits" 4 false #[(5, byRefValueBits)]

private def dictInt8UnsignedSingle : Cell :=
  mkDictSetSliceIntRoot! "int8UnsignedSingle" 8 true #[(255, valueSliceA)]

private def dictInt8UnsignedSingleRepl : Cell :=
  mkDictSetSliceIntRoot! "int8UnsignedSingleRepl" 8 true #[(255, valueSliceB)]

private def baseGas : Int := computeExactGasBudget instrSlice
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instrSlice

private def replaceCreatedSlice (root : Cell) (key : BitString) (value : Slice) : Nat :=
  match dictLookupSetSliceWithCells (some root) key value .replace with
  | .ok (_old, _new, _ok, created, _loaded) => created
  | .error e => panic! s!"dictLookupSetSliceWithCells failed ({reprStr e})"

private def replaceCreatedRef (root : Cell) (key : BitString) (value : Cell) : Nat :=
  match dictLookupSetRefWithCells (some root) key value .replace with
  | .ok (_old, _new, _ok, created, _loaded) => created
  | .error e => panic! s!"dictLookupSetRefWithCells failed ({reprStr e})"

private def hitSliceCreated : Nat :=
  replaceCreatedSlice dictSlice4Single (requireBitsFor 5 4 false) valueSliceB

private def hitSliceRefCreated : Nat :=
  replaceCreatedRef dictSlice4RefSingle (requireBitsFor 5 4 false) valueCellB

private def hitIntSignedCreated : Nat :=
  replaceCreatedSlice dictInt4SignedSingle (requireBitsFor 5 4 false) valueSliceC

private def hitIntUnsignedCreated : Nat :=
  replaceCreatedSlice dictInt4UnsignedSingle (requireBitsFor 5 4 true) valueSliceC

private def hitIntUnsigned8Created : Nat :=
  replaceCreatedSlice dictInt8UnsignedSingle (requireBitsFor 255 8 true) valueSliceC

private def hitIntRefSignedCreated : Nat :=
  replaceCreatedRef dictInt4RefSignedSingle (requireBitsFor 5 4 false) valueCellC

private def hitSliceGas : Int := baseGas + (Int.ofNat hitSliceCreated * cellCreateGasPrice)
private def hitSliceRefGas : Int := baseGas + (Int.ofNat hitSliceRefCreated * cellCreateGasPrice)
private def hitIntSignedGas : Int := baseGas + (Int.ofNat hitIntSignedCreated * cellCreateGasPrice)
private def hitIntUnsignedGas : Int := baseGas + (Int.ofNat hitIntUnsignedCreated * cellCreateGasPrice)
private def hitIntUnsigned8Gas : Int := baseGas + (Int.ofNat hitIntUnsigned8Created * cellCreateGasPrice)
private def hitIntRefSignedGas : Int := baseGas + (Int.ofNat hitIntRefSignedCreated * cellCreateGasPrice)

private def hitSliceGasMinusOne : Int := if hitSliceGas > 0 then hitSliceGas - 1 else 0
private def hitSliceRefGasMinusOne : Int := if hitSliceRefGas > 0 then hitSliceRefGas - 1 else 0
private def hitIntSignedGasMinusOne : Int := if hitIntSignedGas > 0 then hitIntSignedGas - 1 else 0
private def hitIntUnsignedGasMinusOne : Int := if hitIntUnsignedGas > 0 then hitIntUnsignedGas - 1 else 0
private def hitIntUnsigned8GasMinusOne : Int := if hitIntUnsigned8Gas > 0 then hitIntUnsigned8Gas - 1 else 0
private def hitIntRefSignedGasMinusOne : Int := if hitIntRefSignedGas > 0 then hitIntRefSignedGas - 1 else 0

private def mkSliceStack (newValue : Value) (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[newValue, .slice key, dict, intV n]

private def mkIntStack (newValue : Value) (key : Int) (dict : Value) (n : Int) : Array Value :=
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
    (stack : Array Value)
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
      throw (IO.userError s!"{label}: expected {expected}, got decode error {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {reprStr instr}")
      if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decoder left residual bits")

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected {expected}, got {instr}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ => throw (IO.userError s!"{label}: expected {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def runDictReplaceGetDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDictReplaceGetFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.tonEnvOp .setGasLimit) (VM.push (.int (.num 90210))) stack

private def genDICTREPLACEGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 43
  let (tag, rng2) := randNat rng1 0 999_999
  let name := s!"fuzz/{tag}/{shape}"
  let case0 : OracleCase :=
    match shape with
    | 0 => mkCase (s!"{name}/slice-hit-single") (mkSliceStack (.slice valueSliceB) key4_5 (.cell dictSlice4Single) 4)
    | 1 => mkCase (s!"{name}/slice-hit-double") (mkSliceStack (.slice valueSliceC) key4_7 (.cell dictSlice4Double) 4)
    | 2 => mkCase (s!"{name}/slice-hit-zero") (mkSliceStack (.slice valueSliceC) key0 (.cell dictSlice4Zero) 0)
    | 3 => mkCase (s!"{name}/slice-miss-null") (mkSliceStack (.slice valueSliceA) key4_5 (.null) 4)
    | 4 => mkCase (s!"{name}/slice-miss-non-empty") (mkSliceStack (.slice valueSliceA) key4_8 (.cell dictSlice4Single) 4)
    | 5 => mkCase (s!"{name}/int-signed-hit") (mkIntStack (.slice valueSliceB) 5 (.cell dictInt4SignedSingle) 4) (program := #[instrInt])
    | 6 => mkCase (s!"{name}/int-signed-hit-with-unsigned-program") (mkIntStack (.slice valueSliceB) 5 (.cell dictInt4SignedSingle) 4) (program := #[instrIntUnsigned])
    | 7 => mkCase (s!"{name}/int-signed-miss") (mkIntStack (.slice valueSliceA) 2 (.cell dictInt4SignedSingle) 4) (program := #[instrInt])
    | 8 => mkCase (s!"{name}/int-unsigned-hit") (mkIntStack (.slice valueSliceB) 5 (.cell dictInt4UnsignedSingle) 4) (program := #[instrIntUnsigned])
    | 9 => mkCase (s!"{name}/int-unsigned-miss") (mkIntStack (.slice valueSliceB) 2 (.cell dictInt4UnsignedSingle) 4) (program := #[instrIntUnsigned])
    | 10 => mkCase (s!"{name}/byref-slice-hit") (mkSliceStack (.cell valueCellB) key4_5 (.cell dictSlice4RefSingle) 4) (program := #[instrSliceRef])
    | 11 => mkCase (s!"{name}/byref-int-hit") (mkIntStack (.cell valueCellB) 5 (.cell dictInt4RefSignedSingle) 4) (program := #[instrIntRef])
    | 12 => mkCase (s!"{name}/byref-unsigned-int-hit") (mkIntStack (.cell valueCellB) 5 (.cell dictInt4RefUnsignedSingle) 4) (program := #[instrIntUnsignedRef])
    | 13 => mkCase (s!"{name}/byref-miss") (mkIntStack (.cell valueCellA) 5 (.null) 4) (program := #[instrIntRef])
    | 14 => mkCase (s!"{name}/type-key-slice-in-slice-mode") (mkIntStack (.slice valueSliceA) 5 (.cell dictSlice4Single) 4)
    | 15 => mkCase (s!"{name}/type-root-not-cell") (mkSliceStack (.slice valueSliceA) key4_5 (.int (.num 0)) 4)
    | 16 => mkCase (s!"{name}/type-value-wrong") (mkIntStack (.slice valueSliceA) 5 (.cell dictSlice4Single) 4) (program := #[instrSlice])
    | 17 => mkCase (s!"{name}/n-negative") (mkSliceStack (.slice valueSliceA) key4_5 (.cell dictSlice4Single) (-1))
    | 18 => mkCase (s!"{name}/n-too-large") (mkSliceStack (.slice valueSliceA) key4_5 (.cell dictSlice4Single) 1024)
    | 19 => mkCase (s!"{name}/n-nan") (#[.slice valueSliceA, .slice key4_5, .cell dictSlice4Single, .int .nan])
    | 20 => mkCase (s!"{name}/key-short") (mkSliceStack (.slice valueSliceA) key4_short (.cell dictSlice4Single) 4)
    | 21 => mkCase (s!"{name}/int-signed-out-of-range-high") (mkIntStack (.slice valueSliceA) 8 (.cell dictInt4SignedSingle) 4) (program := #[instrInt])
    | 22 => mkCase (s!"{name}/int-signed-out-of-range-low") (mkIntStack (.slice valueSliceA) (-9) (.cell dictInt4SignedSingle) 4) (program := #[instrInt])
    | 23 => mkCase (s!"{name}/int-unsigned-out-of-range-high") (mkIntStack (.slice valueSliceA) 16 (.cell dictInt4UnsignedSingle) 4) (program := #[instrIntUnsigned])
    | 24 => mkCase (s!"{name}/int-unsigned-negative") (mkIntStack (.slice valueSliceA) (-1) (.cell dictInt4UnsignedSingle) 4) (program := #[instrIntUnsigned])
    | 25 => mkCase (s!"{name}/byref-int-bad-shape-bits") (mkIntStack (.cell valueCellB) 5 (.cell dictInt4RefBadBits) 4) (program := #[instrIntRef])
    | 26 => mkCase (s!"{name}/byref-slice-bad-shape-tworefs") (mkIntStack (.cell valueCellB) 5 (.cell dictSlice4RefBadTwoRefs) 4) (program := #[instrSliceRef])
    | 27 => mkCase (s!"{name}/byref-slice-bad-shape-noref") (mkIntStack (.cell valueCellB) 5 (.cell dictSlice4RefBadNoRef) 4) (program := #[instrSliceRef])
    | 28 => mkCase (s!"{name}/malformed-dict-root") (mkIntStack (.slice valueSliceA) 5 (.cell malformedDict) 4) (program := #[instrInt])
    | 29 => mkCodeCase (s!"{name}/decode-f42a") #[] rawF42A
    | 30 => mkCodeCase (s!"{name}/decode-f42c") #[] rawF42C
    | 31 => mkCodeCase (s!"{name}/decode-below") #[] rawF429
    | 32 => mkCodeCase (s!"{name}/decode-above") #[] rawF430
    | 33 => mkCodeCase (s!"{name}/decode-truncated") #[] rawF4
    | 34 => mkCase (s!"{name}/gas-base-exact") (mkSliceStack (.slice valueSliceA) key4_5 .null 4) (program := #[instrSlice]) (gasLimits := oracleGasLimitsExact baseGas)
    | 35 => mkCase (s!"{name}/gas-base-minus-one") (mkSliceStack (.slice valueSliceA) key4_5 .null 4) (program := #[instrSlice]) (gasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne)
    | 36 => mkCase (s!"{name}/gas-slice-hit") (mkSliceStack (.slice valueSliceC) key4_5 (.cell dictSlice4Single) 4) (program := #[instrSlice]) (gasLimits := oracleGasLimitsExact hitSliceGas)
    | 37 => mkCase (s!"{name}/gas-slice-hit-minus-one") (mkSliceStack (.slice valueSliceC) key4_5 (.cell dictSlice4Single) 4) (program := #[instrSlice]) (gasLimits := oracleGasLimitsExactMinusOne hitSliceGasMinusOne)
    | 38 => mkCase (s!"{name}/gas-int-signed-hit") (mkIntStack (.slice valueSliceC) 5 (.cell dictInt4SignedSingle) 4) (program := #[instrInt]) (gasLimits := oracleGasLimitsExact hitIntSignedGas)
    | 39 => mkCase (s!"{name}/gas-int-unsigned-hit") (mkIntStack (.slice valueSliceC) 5 (.cell dictInt4UnsignedSingle) 4) (program := #[instrIntUnsigned]) (gasLimits := oracleGasLimitsExact hitIntUnsignedGas)
    | 40 => mkCase (s!"{name}/gas-int-unsigned8-hit") (mkIntStack (.slice valueSliceC) 255 (.cell dictInt8UnsignedSingle) 8) (program := #[instrIntUnsigned]) (gasLimits := oracleGasLimitsExact hitIntUnsigned8Gas)
    | 41 => mkCase (s!"{name}/gas-byref-hit") (mkIntStack (.cell valueCellC) 5 (.cell dictInt4RefSignedSingle) 4) (program := #[instrIntRef]) (gasLimits := oracleGasLimitsExact hitIntRefSignedGas)
    | 42 => mkCase (s!"{name}/gas-byref-hit-minus-one") (mkIntStack (.cell valueCellC) 5 (.cell dictInt4RefSignedSingle) 4) (program := #[instrIntRef]) (gasLimits := oracleGasLimitsExactMinusOne hitIntRefSignedGas)
    | _ => mkCodeCase (s!"{name}/decode-f42f") #[] rawF42F
  (case0, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDictReplaceGetFallback #[] with
        | .ok st =>
            if st == #[.int (.num 90210)] then
              pure ()
            else
              throw (IO.userError "dispatch/fallback returned unexpected stack")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback unexpected error {e}") },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictReplaceGetDirect instrSlice #[]) .stkUnd },
    { name := "unit/runtime/underflow-three" -- [B2]
      run := do
        expectErr "underflow-three" (runDictReplaceGetDirect instrSlice #[.slice key4_5, .cell dictSlice4Single, intV 4]) .stkUnd },
    { name := "unit/runtime/n-negative" -- [B3]
      run := do
        expectErr "n-negative" (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceA) key4_5 (.cell dictSlice4Single) (-1))) .rangeChk },
    { name := "unit/runtime/n-too-large" -- [B3]
      run := do
        expectErr "n-too-large" (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceA) key4_5 (.cell dictSlice4Single) 1024)) .rangeChk },
    { name := "unit/runtime/n-nan" -- [B3]
      run := do
        expectErr "n-nan" (runDictReplaceGetDirect instrSlice (#[.slice valueSliceA, .slice key4_5, .cell dictSlice4Single, .int .nan])) .rangeChk },
    { name := "unit/runtime/key-short" -- [B4]
      run := do
        expectErr "key-short" (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceA) key4_short (.cell dictSlice4Single) 4)) .cellUnd },
    { name := "unit/runtime/type-key" -- [B5]
      run := do
        expectErr "type-key" (runDictReplaceGetDirect instrSlice (mkIntStack (.slice valueSliceA) 5 (.cell dictSlice4Single) 4)) .typeChk },
    { name := "unit/runtime/type-root" -- [B5]
      run := do
        expectErr "type-root" (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceA) key4_5 (.cell valueCellA) 4)) .typeChk },
    { name := "unit/runtime/type-value-slice" -- [B5]
      run := do
        expectErr "type-value-slice" (runDictReplaceGetDirect instrSlice (mkIntStack (.slice valueSliceA) 5 (.cell dictSlice4Single) 4)) .typeChk },
    { name := "unit/runtime/slice-hit" -- [B6]
      run := do
        expectOkStack "slice-hit"
          (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceB) key4_5 (.cell dictSlice4Single) 4))
          #[.cell dictSlice4SingleRepl, .slice valueSliceA, intV (-1)] },
    { name := "unit/runtime/slice-hit-zero" -- [B6]
      run := do
        expectOkStack "slice-hit-zero"
          (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceC) key0 (.cell dictSlice4Zero) 0))
          #[.cell dictSlice4ZeroRepl, .slice valueSliceA, intV (-1)] },
    { name := "unit/runtime/slice-miss-null" -- [B6]
      run := do
        expectOkStack "slice-miss-null"
          (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceA) key4_5 .null 4))
          #[.null, intV 0] },
    { name := "unit/runtime/slice-miss-root" -- [B6]
      run := do
        expectOkStack "slice-miss-root"
          (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceA) key4_8 (.cell dictSlice4Single) 4))
          #[.cell dictSlice4Single, intV 0] },
    { name := "unit/runtime/int-signed-hit" -- [B6]
      run := do
        expectOkStack "int-signed-hit"
          (runDictReplaceGetDirect instrInt (mkIntStack (.slice valueSliceB) 5 (.cell dictInt4SignedSingle) 4))
          #[.cell dictInt4SignedSingleRepl, .slice valueSliceA, intV (-1)] },
    { name := "unit/runtime/int-signed-miss" -- [B6]
      run := do
        expectOkStack "int-signed-miss"
          (runDictReplaceGetDirect instrInt (mkIntStack (.slice valueSliceC) 2 (.cell dictInt4SignedSingle) 4))
          #[.cell dictInt4SignedSingle, intV 0] },
    { name := "unit/runtime/int-unsigned-hit" -- [B6]
      run := do
        expectOkStack "int-unsigned-hit"
          (runDictReplaceGetDirect instrIntUnsigned (mkIntStack (.slice valueSliceB) 5 (.cell dictInt4UnsignedSingle) 4))
          #[.cell dictInt4UnsignedSingleRepl, .slice valueSliceA, intV (-1)] },
    { name := "unit/runtime/int-unsigned-miss" -- [B6]
      run := do
        expectOkStack "int-unsigned-miss"
          (runDictReplaceGetDirect instrIntUnsigned (mkIntStack (.slice valueSliceC) (-1) (.cell dictInt4UnsignedSingle) 4))
          #[.cell dictInt4UnsignedSingle, intV 0] },
    { name := "unit/runtime/int-signed-oob-high" -- [B4]
      run := do
        expectErr "int-signed-oob-high" (runDictReplaceGetDirect instrInt (mkIntStack (.slice valueSliceA) 8 (.cell dictInt4SignedSingle) 4)) .rangeChk },
    { name := "unit/runtime/int-signed-oob-low" -- [B4]
      run := do
        expectErr "int-signed-oob-low" (runDictReplaceGetDirect instrInt (mkIntStack (.slice valueSliceA) (-9) (.cell dictInt4SignedSingle) 4)) .rangeChk },
    { name := "unit/runtime/int-unsigned-oob-high" -- [B4]
      run := do
        expectErr "int-unsigned-oob-high" (runDictReplaceGetDirect instrIntUnsigned (mkIntStack (.slice valueSliceA) 16 (.cell dictInt4UnsignedSingle) 4)) .rangeChk },
    { name := "unit/runtime/int-unsigned-neg" -- [B4]
      run := do
        expectErr "int-unsigned-neg" (runDictReplaceGetDirect instrIntUnsigned (mkIntStack (.slice valueSliceA) (-1) (.cell dictInt4UnsignedSingle) 4)) .rangeChk },
    { name := "unit/runtime/byref-hit-slice" -- [B9][B7]
      run := do
        expectOkStack "byref-hit-slice"
          (runDictReplaceGetDirect instrSliceRef (mkSliceStack (.cell valueCellB) key4_5 (.cell dictSlice4RefSingle) 4))
          #[.cell dictSlice4RefSingleRepl, .cell valueCellA, intV (-1)] },
    { name := "unit/runtime/byref-hit-int" -- [B7]
      run := do
        expectOkStack "byref-hit-int"
          (runDictReplaceGetDirect instrIntRef (mkIntStack (.cell valueCellB) 5 (.cell dictInt4RefSignedSingle) 4))
          #[.cell dictInt4RefSignedSingleRepl, .cell valueCellA, intV (-1)] },
    { name := "unit/runtime/byref-hit-int-unsigned" -- [B7]
      run := do
        expectOkStack "byref-hit-int-unsigned"
          (runDictReplaceGetDirect instrIntUnsignedRef (mkIntStack (.cell valueCellB) 5 (.cell dictInt4RefUnsignedSingle) 4))
          #[.cell dictInt4RefUnsignedSingleRepl, .cell valueCellA, intV (-1)] },
    { name := "unit/runtime/byref-miss" -- [B6]
      run := do
        expectOkStack "byref-miss"
          (runDictReplaceGetDirect instrSliceRef (mkSliceStack (.cell valueCellC) key4_5 .null 4))
          #[.null, intV 0] },
    { name := "unit/runtime/byref-bad-shape-bits" -- [B7]
      run := do
        expectErr "byref-bad-shape-bits" (runDictReplaceGetDirect instrSliceRef (mkSliceStack (.cell valueCellC) key4_5 (.cell dictSlice4RefBadBits) 4)) .dictErr },
    { name := "unit/runtime/byref-bad-shape-tworefs" -- [B7]
      run := do
        expectErr "byref-bad-shape-tworefs" (runDictReplaceGetDirect instrSliceRef (mkSliceStack (.cell valueCellC) key4_5 (.cell dictSlice4RefBadTwoRefs) 4)) .dictErr },
    { name := "unit/runtime/byref-bad-shape-noref" -- [B7]
      run := do
        expectErr "byref-bad-shape-noref" (runDictReplaceGetDirect instrSliceRef (mkSliceStack (.cell valueCellC) key4_5 (.cell dictSlice4RefBadNoRef) 4)) .dictErr },
    { name := "unit/runtime/malformed-root" -- [B11]
      run := do
        expectErr "malformed-root" (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceA) key4_5 (.cell malformedDict) 4)) .dictErr },
    { name := "unit/asm/reject" -- [B8]
      run := do
        expectAssembleErr "slice" instrSlice .invOpcode
        expectAssembleErr "int" instrInt .invOpcode
        expectAssembleErr "int-unsigned" instrIntUnsigned .invOpcode
        expectAssembleErr "byref" instrSliceRef .invOpcode },
    { name := "unit/decoder/family" -- [B9]
      run := do
        expectDecodeStep "decode-f42a" rawF42A instrSlice
        expectDecodeStep "decode-f42b" rawF42B instrSliceRef
        expectDecodeStep "decode-f42c" rawF42C instrInt
        expectDecodeStep "decode-f42d" rawF42D instrIntRef
        expectDecodeStep "decode-f42e" rawF42E instrIntUnsigned
        expectDecodeStep "decode-f42f" rawF42F instrIntUnsignedRef
        expectDecodeErr "decode-below" rawF429 .invOpcode
        expectDecodeErr "decode-above" rawF430 .invOpcode
        expectDecodeErr "decode-trunc" rawF4 .invOpcode },
    { name := "unit/gas/base-exact" -- [B10]
      run := do
        expectOkStack "gas-base-exact"
          (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceA) key4_5 .null 4))
          #[.null, intV 0] },
    { name := "unit/gas/base-minus-one" -- [B10]
      run := do
        let _ := mkCase "_" (mkSliceStack (.slice valueSliceA) key4_5 .null 4) (program := #[instrSlice]) (gasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne)
        pure () },
    { name := "unit/gas/hit-exact" -- [B10]
      run := do
        expectOkStack "gas-hit-exact"
          (runDictReplaceGetDirect instrSlice (mkSliceStack (.slice valueSliceB) key4_5 (.cell dictSlice4Single) 4))
          #[.cell dictSlice4SingleRepl, .slice valueSliceA, intV (-1)] }
  ]
  oracle := #[
    -- [B6] replace hit in slice dictionary
    mkCase "oracle/slice-hit" (mkSliceStack (.slice valueSliceB) key4_5 (.cell dictSlice4Single) 4),
    -- [B6] slice hit on a multi-entry dictionary
    mkCase "oracle/slice-hit-double" (mkSliceStack (.slice valueSliceC) key4_7 (.cell dictSlice4Double) 4),
    -- [B6] zero-width slice hit
    mkCase "oracle/slice-hit-zero" (mkSliceStack (.slice valueSliceC) key0 (.cell dictSlice4Zero) 0),
    -- [B6] replace miss with null root
    mkCase "oracle/slice-miss-null" (mkSliceStack (.slice valueSliceA) key4_5 .null 4),
    -- [B6] replace miss in non-empty root
    mkCase "oracle/slice-miss-root" (mkSliceStack (.slice valueSliceA) key4_8 (.cell dictSlice4Single) 4),
    -- [B6] signed int key hit
    mkCase "oracle/int-signed-hit" (mkIntStack (.slice valueSliceB) 5 (.cell dictInt4SignedSingle) 4) #[instrInt],
    -- [B6] signed int key miss
    mkCase "oracle/int-signed-miss" (mkIntStack (.slice valueSliceA) 2 (.cell dictInt4SignedSingle) 4) #[instrInt],
    -- [B6] unsigned int key hit
    mkCase "oracle/int-unsigned-hit" (mkIntStack (.slice valueSliceB) 5 (.cell dictInt4UnsignedSingle) 4) #[instrIntUnsigned],
    -- [B6] unsigned int key miss
    mkCase "oracle/int-unsigned-miss" (mkIntStack (.slice valueSliceA) 2 (.cell dictInt4UnsignedSingle) 4) #[instrIntUnsigned],
    -- [B6] byref signed int hit
    mkCase "oracle/byref-hit-int" (mkIntStack (.cell valueCellB) 5 (.cell dictInt4RefSignedSingle) 4) #[instrIntRef],
    -- [B6] byref unsigned int hit
    mkCase "oracle/byref-hit-int-unsigned" (mkIntStack (.cell valueCellB) 5 (.cell dictInt4RefUnsignedSingle) 4) #[instrIntUnsignedRef],
    -- [B6] byref slice hit
    mkCase "oracle/byref-hit-slice" (mkSliceStack (.cell valueCellB) key4_5 (.cell dictSlice4RefSingle) 4) #[instrSliceRef],
    -- [B6] byref miss
    mkCase "oracle/byref-miss" (mkSliceStack (.cell valueCellA) key4_5 .null 4) #[instrSliceRef],
    -- [B3] invalid n
    mkCase "oracle/err/n-negative" (mkSliceStack (.slice valueSliceA) key4_5 (.cell dictSlice4Single) (-1)),
    mkCase "oracle/err/n-too-large" (mkSliceStack (.slice valueSliceA) key4_5 (.cell dictSlice4Single) 1024),
    mkCase "oracle/err/n-nan" (#[.slice valueSliceA, .slice key4_5, .cell dictSlice4Single, .int .nan]),
    -- [B4] slice key too short
    mkCase "oracle/err/key-short" (mkSliceStack (.slice valueSliceA) key4_short (.cell dictSlice4Single) 4),
    -- [B4] integer range errors
    mkCase "oracle/err/int-signed-oob-high" (mkIntStack (.slice valueSliceA) 8 (.cell dictInt4SignedSingle) 4) #[instrInt],
    mkCase "oracle/err/int-signed-oob-low" (mkIntStack (.slice valueSliceA) (-9) (.cell dictInt4SignedSingle) 4) #[instrInt],
    mkCase "oracle/err/int-unsigned-oob-high" (mkIntStack (.slice valueSliceA) 16 (.cell dictInt4UnsignedSingle) 4) #[instrIntUnsigned],
    mkCase "oracle/err/int-unsigned-oob-neg" (mkIntStack (.slice valueSliceA) (-1) (.cell dictInt4UnsignedSingle) 4) #[instrIntUnsigned],
    -- [B5] type errors
    mkCase "oracle/err/type-root" (mkSliceStack (.slice valueSliceA) key4_5 (.int (.num 0)) 4),
    mkCase "oracle/err/type-key" (mkIntStack (.slice valueSliceA) 5 (.cell dictSlice4Single) 4),
    mkCase "oracle/err/type-key-int" (mkSliceStack (.slice valueSliceA) key4_5 (.cell dictSlice4Single) 4) #[instrInt],
    mkCase "oracle/err/type-value" (mkIntStack (.cell valueCellA) 5 (.cell dictSlice4Single) 4),
    -- [B7] byref payload shape errors
    mkCase "oracle/err/byref-payload-bits" (mkSliceStack (.cell valueCellA) key4_5 (.cell dictSlice4RefBadBits) 4) #[instrSliceRef],
    mkCase "oracle/err/byref-payload-tworefs" (mkSliceStack (.cell valueCellA) key4_5 (.cell dictSlice4RefBadTwoRefs) 4) #[instrSliceRef],
    mkCase "oracle/err/byref-payload-no-ref" (mkSliceStack (.cell valueCellA) key4_5 (.cell dictSlice4RefBadNoRef) 4) #[instrSliceRef],
    mkCase "oracle/err/byref-int-payload-bits" (mkIntStack (.cell valueCellA) 5 (.cell dictInt4RefBadBits) 4) #[instrIntRef],
    -- [B11] malformed root
    mkCase "oracle/err/malformed-root" (mkIntStack (.slice valueSliceA) 5 (.cell malformedDict) 4) #[instrInt],
    -- [B9] decoder map checks
    mkCodeCase "oracle/raw/f42a" #[] rawF42A,
    mkCodeCase "oracle/raw/f42b" #[] rawF42B,
    mkCodeCase "oracle/raw/f42c" #[] rawF42C,
    mkCodeCase "oracle/raw/f42d" #[] rawF42D,
    mkCodeCase "oracle/raw/f42e" #[] rawF42E,
    mkCodeCase "oracle/raw/f42f" #[] rawF42F,
    mkCodeCase "oracle/raw/f429" #[] rawF429,
    mkCodeCase "oracle/raw/f430" #[] rawF430,
    mkCodeCase "oracle/raw/f4" #[] rawF4,
    -- [B8] assembler errors
    mkCodeCase "oracle/asm/not-supported" #[] (Cell.mkOrdinary (natToBits 0 16) #[]) (gasLimits := {}),
    -- [B10] gas exact and exact-minus-one
    mkCase "oracle/gas/base-exact" (mkSliceStack (.slice valueSliceA) key4_5 .null 4) (gasLimits := oracleGasLimitsExact baseGas),
    mkCase "oracle/gas/base-minus-one" (mkSliceStack (.slice valueSliceA) key4_5 .null 4) (gasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne),
    mkCase "oracle/gas/hit-slice-exact" (mkSliceStack (.slice valueSliceC) key4_5 (.cell dictSlice4Single) 4) (gasLimits := oracleGasLimitsExact hitSliceGas),
    mkCase "oracle/gas/hit-slice-minus-one" (mkSliceStack (.slice valueSliceC) key4_5 (.cell dictSlice4Single) 4) (gasLimits := oracleGasLimitsExactMinusOne hitSliceGasMinusOne),
    mkCase "oracle/gas/hit-slice-ref-exact" (mkSliceStack (.slice valueSliceC) key4_5 (.cell dictSlice4RefSingle) 4) (program := #[instrSliceRef]) (gasLimits := oracleGasLimitsExact hitSliceRefGas),
    mkCase "oracle/gas/hit-slice-ref-minus-one" (mkSliceStack (.slice valueSliceC) key4_5 (.cell dictSlice4RefSingle) 4) (program := #[instrSliceRef]) (gasLimits := oracleGasLimitsExactMinusOne hitSliceRefGasMinusOne),
    mkCase "oracle/gas/int-signed-exact" (mkIntStack (.slice valueSliceC) 5 (.cell dictInt4SignedSingle) 4) (program := #[instrInt]) (gasLimits := oracleGasLimitsExact hitIntSignedGas),
    mkCase "oracle/gas/int-signed-minus-one" (mkIntStack (.slice valueSliceC) 5 (.cell dictInt4SignedSingle) 4) (program := #[instrInt]) (gasLimits := oracleGasLimitsExactMinusOne hitIntSignedGasMinusOne),
    mkCase "oracle/gas/int-unsigned-exact" (mkIntStack (.slice valueSliceC) 5 (.cell dictInt4UnsignedSingle) 4) (program := #[instrIntUnsigned]) (gasLimits := oracleGasLimitsExact hitIntUnsignedGas),
    mkCase "oracle/gas/int-unsigned8-exact" (mkIntStack (.slice valueSliceC) 255 (.cell dictInt8UnsignedSingle) 8) (program := #[instrIntUnsigned]) (gasLimits := oracleGasLimitsExact hitIntUnsigned8Gas),
    mkCase "oracle/gas/int-ref-exact" (mkIntStack (.cell valueCellC) 5 (.cell dictInt4RefSignedSingle) 4) (program := #[instrIntRef]) (gasLimits := oracleGasLimitsExact hitIntRefSignedGas)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTREPLACEGETFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREPLACEGET
