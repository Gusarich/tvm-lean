import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTSET

/-!
INSTRUCTION: DICTSET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictDictSet` matches only `.dictSet` constructors.

2. [B2] Stack arity guard.
   - `checkUnderflow 4` must run before any pops.

3. [B3] Width (`n`) parsing and range checks.
   - Width parsing is via `popNatUpTo 1023`.
   - Width must be a finite int in `[0,1023]`; otherwise `.rangeChk`.

4. [B4] Dictionary root shape.
   - `popMaybeCell` accepts only `.null` and `.cell`.
   - Anything else is `.typeChk`.

5. [B5] Non-int key path (`intKey=false`).
   - Key is a slice; exactly `n` bits are consumed.
   - If too short, `.cellUnd`.

6. [B6] Int key path (`intKey=true`).
   - `dictKeyBits?` validates signed / unsigned range.
   - Signed and unsigned overflow produce `.rangeChk`.
   - `.nan` key produces `.rangeChk`.

7. [B7] Value stack-shape branch.
   - `.byRef=false` requires a `.slice`.
   - `.byRef=true` requires a `.cell`.

8. [B8] `.set` semantics.
   - Rewrites/insert and pushes new root.
   - On internal helper failure, `.fatal` is raised.

9. [B9] `.replace` semantics.
   - On hit: pushes updated root and `-1`.
   - On miss: keeps root unchanged (or `.null`) and pushes `0`.

10. [B10] `.add` semantics.
    - On miss: inserts and pushes new root and `-1`.
    - On hit: root unchanged and `0`.

11. [B11] Malformed dictionary error propagation.
    - Invalid existing roots can raise `.dictErr`.

12. [B12] Assembler constraints and valid encodings.
    - Supported opcodes:
      - `.dictSet` set: `0xF412..0xF417`
      - `.dictSet` replace: `0xF422..0xF427`
      - `.dictSet` add: `0xF432..0xF437`
    - `.dictSet false true ...` is invalid.

13. [B13] Decoder boundaries.
    - Adjacent boundaries around each family decode to `.invOpcode`.
    - `0xF4` truncated form must decode to `.invOpcode`.

14. [B14] Gas accounting.
    - `computeExactGasBudget` plus `created * cellCreateGasPrice`.
    - Both exact and exact-1 limits are required across success branches.

TOTAL BRANCHES: 14
-/

private def suiteId : InstrId :=
  { name := "DICTSET" }

private def dictSetSlice : Instr := .dictSet false false false .set
private def dictSetSliceRef : Instr := .dictSet false false true .set
private def dictSetSigned : Instr := .dictSet true false false .set
private def dictSetSignedRef : Instr := .dictSet true false true .set
private def dictSetUnsigned : Instr := .dictSet true true false .set
private def dictSetUnsignedRef : Instr := .dictSet true true true .set

private def dictReplaceSlice : Instr := .dictSet false false false .replace
private def dictReplaceSliceRef : Instr := .dictSet false false true .replace
private def dictReplaceSigned : Instr := .dictSet true false false .replace
private def dictReplaceSignedRef : Instr := .dictSet true false true .replace
private def dictReplaceUnsigned : Instr := .dictSet true true false .replace
private def dictReplaceUnsignedRef : Instr := .dictSet true true true .replace

private def dictAddSlice : Instr := .dictSet false false false .add
private def dictAddSliceRef : Instr := .dictSet false false true .add
private def dictAddSigned : Instr := .dictSet true false false .add
private def dictAddSignedRef : Instr := .dictSet true false true .add
private def dictAddUnsigned : Instr := .dictSet true true false .add
private def dictAddUnsignedRef : Instr := .dictSet true true true .add

private def dispatchSentinel : Int := 13_021

private def opcodeSlice16 (w : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w 16) #[])

private def raw412 : Cell := Cell.mkOrdinary (natToBits 0xF412 16) #[]
private def raw413 : Cell := Cell.mkOrdinary (natToBits 0xF413 16) #[]
private def raw414 : Cell := Cell.mkOrdinary (natToBits 0xF414 16) #[]
private def raw415 : Cell := Cell.mkOrdinary (natToBits 0xF415 16) #[]
private def raw416 : Cell := Cell.mkOrdinary (natToBits 0xF416 16) #[]
private def raw417 : Cell := Cell.mkOrdinary (natToBits 0xF417 16) #[]
private def raw421 : Cell := Cell.mkOrdinary (natToBits 0xF421 16) #[]
private def raw418 : Cell := Cell.mkOrdinary (natToBits 0xF418 16) #[]
private def raw422 : Cell := Cell.mkOrdinary (natToBits 0xF422 16) #[]
private def raw423 : Cell := Cell.mkOrdinary (natToBits 0xF423 16) #[]
private def raw424 : Cell := Cell.mkOrdinary (natToBits 0xF424 16) #[]
private def raw425 : Cell := Cell.mkOrdinary (natToBits 0xF425 16) #[]
private def raw426 : Cell := Cell.mkOrdinary (natToBits 0xF426 16) #[]
private def raw427 : Cell := Cell.mkOrdinary (natToBits 0xF427 16) #[]
private def raw428 : Cell := Cell.mkOrdinary (natToBits 0xF428 16) #[]
private def raw431 : Cell := Cell.mkOrdinary (natToBits 0xF431 16) #[]
private def raw432 : Cell := Cell.mkOrdinary (natToBits 0xF432 16) #[]
private def raw433 : Cell := Cell.mkOrdinary (natToBits 0xF433 16) #[]
private def raw434 : Cell := Cell.mkOrdinary (natToBits 0xF434 16) #[]
private def raw435 : Cell := Cell.mkOrdinary (natToBits 0xF435 16) #[]
private def raw436 : Cell := Cell.mkOrdinary (natToBits 0xF436 16) #[]
private def raw437 : Cell := Cell.mkOrdinary (natToBits 0xF437 16) #[]
private def raw438 : Cell := Cell.mkOrdinary (natToBits 0xF438 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def sampleSliceA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def sampleSliceB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def sampleSliceC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def sampleSliceD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def sampleSliceE : Slice := mkSliceFromBits (natToBits 0xE5 8)

private def sampleCellA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def sampleCellB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def sampleCellC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def sampleCellD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]
private def sampleCellE : Cell := Cell.mkOrdinary (natToBits 0xE5 8) #[]
private def sampleCellF : Cell := Cell.mkOrdinary (natToBits 0xF6 8) #[]

private def malformedDictCell : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def requireBits (label : String) (key : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? key n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: key out of range ({key}) for n={n} unsigned={unsigned}"

private def mkDictSliceRoot! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    entries.foldl
      (fun st e =>
        let (k, v) := e
        match st with
        | some root =>
            match dictSetSliceWithCells (some root) k v .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            match dictSetSliceWithCells none k v .set with
            | .ok (some next, _, _, _) => some next
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to construct slice dictionary"

private def mkDictRefRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  let rootOpt : Option Cell :=
    entries.foldl
      (fun st e =>
        let (k, v) := e
        match st with
        | some root =>
            match dictSetRefWithCells (some root) k v .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            match dictSetRefWithCells none k v .set with
            | .ok (some next, _, _, _) => some next
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to construct ref dictionary"

private def mkDictIntSliceRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Slice)) : Cell :=
  mkDictSliceRoot! label
    (entries.map fun e =>
      let (k, v) := e
      (requireBits label k n unsigned, v))

private def mkDictIntRefRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Cell)) : Cell :=
  mkDictRefRoot! label
    (entries.map fun e =>
      let (k, v) := e
      (requireBits label k n unsigned, v))

private def dictSlice4Root : Cell :=
  mkDictSliceRoot! "dictSlice4Root" #[
    (natToBits 0 4, sampleSliceA),
    (natToBits 1 4, sampleSliceB),
    (natToBits 15 4, sampleSliceC)
  ]

private def dictSlice8Root : Cell :=
  mkDictSliceRoot! "dictSlice8Root" #[
    (natToBits 5 8, sampleSliceA),
    (natToBits 6 8, sampleSliceB),
    (natToBits 255 8, sampleSliceC)
  ]

private def dictSlice8 : Cell := dictSlice8Root

private def dictSlice0Root : Cell :=
  mkDictSliceRoot! "dictSlice0Root" #[(#[], sampleSliceD)]

private def dictSlice8SharedFork : Cell :=
  mkDictSliceRoot! "dictSlice8SharedFork" #[
    (natToBits 0 8, sampleSliceA),
    (natToBits 128 8, sampleSliceB)
  ]

private def dictRef8Root : Cell :=
  mkDictRefRoot! "dictRef8Root" #[
    (natToBits 5 8, sampleCellA),
    (natToBits 6 8, sampleCellB),
    (natToBits 128 8, sampleCellC)
  ]

private def dictInt8Signed : Cell :=
  mkDictIntSliceRoot! "dictInt8Signed" 8 false #[
    (5, sampleSliceA),
    (6, sampleSliceB),
    (-1, sampleSliceC)
  ]

private def dictInt8Unsigned : Cell :=
  mkDictIntSliceRoot! "dictInt8Unsigned" 8 true #[
    (0, sampleSliceA),
    (7, sampleSliceB),
    (255, sampleSliceC)
  ]

private def dictInt8SignedRef : Cell :=
  mkDictIntRefRoot! "dictInt8SignedRef" 8 false #[
    (5, sampleCellA),
    (6, sampleCellB),
    (-1, sampleCellC)
  ]

private def dictInt8UnsignedRef : Cell :=
  mkDictIntRefRoot! "dictInt8UnsignedRef" 8 true #[
    (0, sampleCellA),
    (7, sampleCellB),
    (255, sampleCellC)
  ]

private def dictSetSliceExpected! (root : Option Cell) (keyBits : BitString) (value : Slice) (mode : DictSetMode) : Cell :=
  match dictSetSliceWithCells root keyBits value mode with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) => panic! "DICTSET: expected root for slice insertion"
  | .error e => panic! s!"DICTSET: dictSetSliceWithCells failed: {reprStr e}"

private def dictSetRefExpected! (root : Option Cell) (keyBits : BitString) (value : Cell) (mode : DictSetMode) : Cell :=
  match dictSetRefWithCells root keyBits value mode with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) => panic! "DICTSET: expected root for ref insertion"
  | .error e => panic! s!"DICTSET: dictSetRefWithCells failed: {reprStr e}"

private def dictSetSliceIntExpected! (root : Option Cell) (n : Nat) (unsigned : Bool) (key : Int) (value : Slice) (mode : DictSetMode) : Cell :=
  dictSetSliceExpected! root (requireBits "dictSetSliceIntExpected" key n unsigned) value mode

private def dictSetRefIntExpected! (root : Option Cell) (n : Nat) (unsigned : Bool) (key : Int) (value : Cell) (mode : DictSetMode) : Cell :=
  dictSetRefExpected! root (requireBits "dictSetRefIntExpected" key n unsigned) value mode

private def dictSetSliceCreated (root : Option Cell) (keyBits : BitString) (value : Slice) (mode : DictSetMode) : Nat :=
  match dictSetSliceWithCells root keyBits value mode with
  | .ok (_, _, created, _) => created
  | .error e => panic! s!"DICTSET: dictSetSliceWithCells failed: {reprStr e}"

private def dictSetRefCreated (root : Option Cell) (keyBits : BitString) (value : Cell) (mode : DictSetMode) : Nat :=
  match dictSetRefWithCells root keyBits value mode with
  | .ok (_, _, created, _) => created
  | .error e => panic! s!"DICTSET: dictSetRefWithCells failed: {reprStr e}"

private def dictSetSliceIntCreated (root : Option Cell) (n : Nat) (unsigned : Bool) (key : Int) (value : Slice) (mode : DictSetMode) : Nat :=
  dictSetSliceCreated root (requireBits "dictSetSliceIntCreated" key n unsigned) value mode

private def dictSetRefIntCreated (root : Option Cell) (n : Nat) (unsigned : Bool) (key : Int) (value : Cell) (mode : DictSetMode) : Nat :=
  dictSetRefCreated root (requireBits "dictSetRefIntCreated" key n unsigned) value mode

private def runDictSet (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def runDictSetFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictSetSlice])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    initStack := stack
    program := program
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    initStack := stack
    instr := suiteId
    codeCell? := some code
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasProgram (gas : Int) (instr : Instr) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]

private def mkSliceStack (value : Slice) (keyBits : BitString) (dict : Value) (n : Int) : Array Value :=
  #[(.slice value), .slice (mkSliceFromBits keyBits), dict, intV n]

private def mkRefStack (value : Cell) (keyBits : BitString) (dict : Value) (n : Int) : Array Value :=
  #[(.cell value), .slice (mkSliceFromBits keyBits), dict, intV n]

private def mkIntStack (value : Value) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[value, intV key, dict, intV n]

private def expectAssembleEq (label : String) (code : Cell) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      if c.bits = code.bits then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {code.bits}, got {c.bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")

private def expectAssembleInv (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok c =>
      throw (IO.userError s!"{label}: expected assembler rejection, got {reprStr c}")

private def expectDecodeInv (label : String) (c : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell c) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (i, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr i} with {bits} bits")

private def expectDecodeEq (label : String) (w : Nat) (instr : Instr) : IO Unit := do
  let s := opcodeSlice16 w
  let _ ← expectDecodeStep label s instr 16
  pure ()

private def setSliceBase : Int := computeExactGasBudget dictSetSlice
private def setSignedBase : Int := computeExactGasBudget dictSetSigned
private def setUnsignedBase : Int := computeExactGasBudget dictSetUnsigned
private def setRefBase : Int := computeExactGasBudget dictSetSliceRef

private def replaceSliceBase : Int := computeExactGasBudget dictReplaceSlice
private def replaceSignedBase : Int := computeExactGasBudget dictReplaceSigned
private def replaceUnsignedBase : Int := computeExactGasBudget dictReplaceUnsigned
private def replaceRefBase : Int := computeExactGasBudget dictReplaceSliceRef

private def addSliceBase : Int := computeExactGasBudget dictAddSlice
private def addSignedBase : Int := computeExactGasBudget dictAddSigned
private def addUnsignedBase : Int := computeExactGasBudget dictAddUnsigned
private def addRefBase : Int := computeExactGasBudget dictAddSliceRef

private def setSliceInsertCreated : Nat := dictSetSliceCreated none (natToBits 34 8) sampleSliceD .set
private def setSignedInsertCreated : Nat := dictSetSliceIntCreated none 8 false 12 sampleSliceD .set
private def setUnsignedInsertCreated : Nat := dictSetSliceIntCreated none 8 true 34 sampleSliceD .set
private def setRefInsertCreated : Nat := dictSetRefCreated none (natToBits 34 8) sampleCellD .set

private def replaceSliceHitCreated : Nat := dictSetSliceCreated (some dictSlice8) (natToBits 5 8) sampleSliceD .replace
private def replaceSignedHitCreated : Nat := dictSetSliceIntCreated (some dictInt8Signed) 8 false 5 sampleSliceD .replace
private def replaceUnsignedHitCreated : Nat := dictSetSliceIntCreated (some dictInt8Unsigned) 8 true 5 sampleSliceD .replace
private def replaceRefHitCreated : Nat := dictSetRefIntCreated (some dictInt8SignedRef) 8 false 5 sampleCellD .replace

private def addSliceInsertCreated : Nat := dictSetSliceCreated none (natToBits 39 8) sampleSliceD .add
private def addSignedInsertCreated : Nat := dictSetSliceIntCreated none 8 false 12 sampleSliceD .add
private def addUnsignedInsertCreated : Nat := dictSetSliceIntCreated none 8 true 39 sampleSliceD .add
private def addRefInsertCreated : Nat := dictSetRefCreated none (natToBits 39 8) sampleCellD .add

private def setSliceGas : Int := setSliceBase + Int.ofNat setSliceInsertCreated * cellCreateGasPrice
private def setSignedGas : Int := setSignedBase + Int.ofNat setSignedInsertCreated * cellCreateGasPrice
private def setUnsignedGas : Int := setUnsignedBase + Int.ofNat setUnsignedInsertCreated * cellCreateGasPrice
private def setRefGas : Int := setRefBase + Int.ofNat setRefInsertCreated * cellCreateGasPrice

private def replaceSliceHitGas : Int := replaceSliceBase + Int.ofNat replaceSliceHitCreated * cellCreateGasPrice
private def replaceSignedHitGas : Int := replaceSignedBase + Int.ofNat replaceSignedHitCreated * cellCreateGasPrice
private def replaceUnsignedHitGas : Int := replaceUnsignedBase + Int.ofNat replaceUnsignedHitCreated * cellCreateGasPrice
private def replaceRefHitGas : Int := replaceRefBase + Int.ofNat replaceRefHitCreated * cellCreateGasPrice

private def addSliceGas : Int := addSliceBase + Int.ofNat addSliceInsertCreated * cellCreateGasPrice
private def addSignedGas : Int := addSignedBase + Int.ofNat addSignedInsertCreated * cellCreateGasPrice
private def addUnsignedGas : Int := addUnsignedBase + Int.ofNat addUnsignedInsertCreated * cellCreateGasPrice
private def addRefGas : Int := addRefBase + Int.ofNat addRefInsertCreated * cellCreateGasPrice

private def setSliceGasMinusOne : Int := if setSliceGas > 0 then setSliceGas - 1 else 0
private def setSignedGasMinusOne : Int := if setSignedGas > 0 then setSignedGas - 1 else 0
private def setUnsignedGasMinusOne : Int := if setUnsignedGas > 0 then setUnsignedGas - 1 else 0
private def setRefGasMinusOne : Int := if setRefGas > 0 then setRefGas - 1 else 0

private def replaceSliceHitGasMinusOne : Int := if replaceSliceHitGas > 0 then replaceSliceHitGas - 1 else 0
private def replaceSliceMissGasMinusOne : Int := if replaceSliceBase > 0 then replaceSliceBase - 1 else 0
private def replaceSignedHitGasMinusOne : Int := if replaceSignedHitGas > 0 then replaceSignedHitGas - 1 else 0
private def replaceUnsignedHitGasMinusOne : Int := if replaceUnsignedHitGas > 0 then replaceUnsignedHitGas - 1 else 0

private def addSliceGasMinusOne : Int := if addSliceGas > 0 then addSliceGas - 1 else 0
private def addSignedGasMinusOne : Int := if addSignedGas > 0 then addSignedGas - 1 else 0
private def addUnsignedGasMinusOne : Int := if addUnsignedGas > 0 then addUnsignedGas - 1 else 0
private def addRefGasMinusOne : Int := if addRefGas > 0 then addRefGas - 1 else 0

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

private def genDICTSETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    (mkCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 1 then
    (mkCase "fuzz/underflow/one" #[intV 8], rng2)
  else if shape = 2 then
    (mkCase "fuzz/underflow/two" #[.slice sampleSliceA, .slice sampleSliceB, .null], rng2)
  else if shape = 3 then
    (mkCase "fuzz/underflow/three" (mkSliceStack sampleSliceA (natToBits 5 8) .null 8), rng2)
  else if shape = 4 then
    (mkCase "fuzz/n-negative" (mkSliceStack sampleSliceA (natToBits 5 8) .null (-1)) (#[dictSetSlice]), rng2)
  else if shape = 5 then
    (mkCase "fuzz/n-too-large" (mkSliceStack sampleSliceA (natToBits 5 8) .null 1024) (#[dictSetSlice]), rng2)
  else if shape = 6 then
    (mkCase "fuzz/n-nan" #[.slice sampleSliceA, .slice sampleSliceA, .null, .int .nan] (#[dictSetSlice]), rng2)
  else if shape = 7 then
    (mkCase "fuzz/dict-not-maybe-cell" (mkSliceStack sampleSliceA (natToBits 5 8) (.tuple #[]) 8) (#[dictSetSlice]), rng2)
  else if shape = 8 then
    (mkCase "fuzz/key-not-slice" (mkIntStack (.slice sampleSliceA) 5 .null 8) (#[dictSetSlice]), rng2)
  else if shape = 9 then
    (mkCase "fuzz/key-not-int" ((mkSliceStack sampleSliceA (natToBits 5 8) .null 8) |> fun st => #[.slice sampleSliceA, .int (.num 5), st[2]!, intV 8]) (#[dictSetSigned]), rng2)
  else if shape = 10 then
    (mkCase "fuzz/value-not-slice" (mkIntStack (.cell sampleCellA) 5 .null 8) (#[dictSetSigned]), rng2)
  else if shape = 11 then
    (mkCase "fuzz/value-not-cell" (mkIntStack (.slice sampleSliceA) 5 (.null) 8) (#[dictSetSignedRef]), rng2)
  else if shape = 12 then
    (mkCase "fuzz/slice-key-short" (mkSliceStack sampleSliceA (natToBits 5 3) .null 8) (#[dictSetSlice]), rng2)
  else if shape = 13 then
    (mkCase "fuzz/int-key-nan" #[.slice sampleSliceA, .int .nan, .null, intV 8] (#[dictSetSigned]), rng2)
  else if shape = 14 then
    (mkCase "fuzz/int-key-oob-signed-high" (mkIntStack (.slice sampleSliceA) 128 .null 8) (#[dictSetSigned]), rng2)
  else if shape = 15 then
    (mkCase "fuzz/int-key-oob-signed-low" (mkIntStack (.slice sampleSliceA) (-129) .null 8) (#[dictSetSigned]), rng2)
  else if shape = 16 then
    (mkCase "fuzz/int-key-oob-unsigned-high" (mkIntStack (.slice sampleSliceA) 256 .null 8) (#[dictSetUnsigned]), rng2)
  else if shape = 17 then
    (mkCase "fuzz/int-key-oob-unsigned-neg" (mkIntStack (.slice sampleSliceA) (-1) .null 8) (#[dictSetUnsigned]), rng2)
  else if shape = 18 then
    (mkCase "fuzz/set/slice-hit" (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8) (#[dictSetSlice]), rng2)
  else if shape = 19 then
    (mkCase "fuzz/set/slice-miss" (mkSliceStack sampleSliceD (natToBits 9 8) (.null) 8) (#[dictSetSlice]), rng2)
  else if shape = 20 then
    (mkCase "fuzz/set/ref-hit" (mkRefStack sampleCellD (natToBits 6 8) (.cell dictRef8Root) 8) (#[dictSetSliceRef]), rng2)
  else if shape = 21 then
    (mkCase "fuzz/replace/slice-hit" (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8) (#[dictReplaceSlice]), rng2)
  else if shape = 22 then
    (mkCase "fuzz/replace/slice-miss" (mkSliceStack sampleSliceD (natToBits 9 8) (.cell dictSlice8) 8) (#[dictReplaceSlice]), rng2)
  else if shape = 23 then
    (mkCase "fuzz/replace/signed-hit" (mkIntStack (.slice sampleSliceD) 6 (.cell dictInt8Signed) 8) (#[dictReplaceSigned]), rng2)
  else if shape = 24 then
    (mkCase "fuzz/replace/unsigned-hit" (mkIntStack (.slice sampleSliceD) 7 (.cell dictInt8Unsigned) 8) (#[dictReplaceUnsigned]), rng2)
  else if shape = 25 then
    (mkCase "fuzz/add/slice-miss" (mkSliceStack sampleSliceD (natToBits 10 8) (.null) 8) (#[dictAddSlice]), rng2)
  else if shape = 26 then
    (mkCase "fuzz/add/slice-hit" (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8) (#[dictAddSlice]), rng2)
  else if shape = 27 then
    (mkCase "fuzz/add/ref-miss" (mkRefStack sampleCellD (natToBits 10 8) (.null) 8) (#[dictAddSliceRef]), rng2)
  else if shape = 28 then
    (mkCase "fuzz/add/ref-hit" (mkRefStack sampleCellA (natToBits 5 8) (.cell dictRef8Root) 8) (#[dictAddSliceRef]), rng2)
  else if shape = 29 then
    (mkCase "fuzz/malformed-root-slice" (mkSliceStack sampleSliceD (natToBits 5 8) (.cell malformedDictCell) 8) (#[dictSetSlice]), rng2)
  else if shape = 30 then
    (mkCase "fuzz/malformed-root-ref" (mkRefStack sampleCellD (natToBits 5 8) (.cell malformedDictCell) 8) (#[dictSetSliceRef]), rng2)
  else if shape = 31 then
    (mkCodeCase "fuzz/decode/412" #[] raw412, rng2)
  else if shape = 32 then
    (mkCodeCase (s!"fuzz/decode/425/{tag}") #[] raw425, rng2)
  else if shape = 33 then
    (mkCodeCase (s!"fuzz/decode/436/{tag}") #[] raw436, rng2)
  else if shape = 34 then
    (mkCase (s!"fuzz/gas/set-slice-exact/{tag}") (mkSliceStack sampleSliceD (natToBits 10 8) (.null) 8) (mkGasProgram setSliceGas dictSetSlice) (oracleGasLimitsExact setSliceGas), rng2)
  else if shape = 35 then
    (mkCase (s!"fuzz/gas/set-slice-minus/{tag}") (mkSliceStack sampleSliceD (natToBits 10 8) (.null) 8) (mkGasProgram setSliceGasMinusOne dictSetSlice) (oracleGasLimitsExactMinusOne setSliceGasMinusOne), rng2)
  else if shape = 36 then
    (mkCase (s!"fuzz/gas/replace-signed-hit/{tag}") (mkIntStack (.slice sampleSliceD) 6 (.cell dictInt8Signed) 8) (mkGasProgram replaceSignedHitGas dictReplaceSigned) (oracleGasLimitsExact replaceSignedHitGas), rng2)
  else if shape = 37 then
    (mkCase (s!"fuzz/gas/add-unsigned-miss/{tag}") (mkIntStack (.slice sampleSliceD) 9 (.null) 8) (mkGasProgram addUnsignedGas dictAddUnsigned) (oracleGasLimitsExact addUnsignedGas), rng2)
  else
    (mkCase (s!"fuzz/gas/add-unsigned-minus/{tag}") (mkIntStack (.slice sampleSliceD) 9 (.null) 8) (mkGasProgram addUnsignedGasMinusOne dictAddUnsigned) (oracleGasLimitsExactMinusOne addUnsignedGasMinusOne), rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "dispatch/fallback"
          (runDictSetFallback #[
            .slice sampleSliceA,
            .int (.num 5),
            .cell sampleCellA,
            intV 8
          ])
          (#[
            .slice sampleSliceA,
            .int (.num 5),
            .cell sampleCellA,
            intV 8,
            intV dispatchSentinel
          ]) },
    { name := "unit/underflow/empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictSet dictSetSlice #[]) .stkUnd },
    { name := "unit/underflow/one" -- [B2]
      run := do
        expectErr "underflow-one" (runDictSet dictSetSlice #[.slice sampleSliceA]) .stkUnd },
    { name := "unit/underflow/two" -- [B2]
      run := do
        expectErr "underflow-two" (runDictSet dictSetSlice #[.slice sampleSliceA, intV 5]) .stkUnd },
    { name := "unit/underflow/three" -- [B2]
      run := do
        expectErr "underflow-three" (runDictSet dictSetSlice #[.slice sampleSliceA, intV 5, .null]) .stkUnd },
    { name := "unit/n/nan" -- [B3]
      run := do
        expectErr "n-nan" (runDictSet dictSetSlice #[.slice sampleSliceA, .slice (mkSliceFromBits (natToBits 5 8)), .null, .int .nan]) .rangeChk },
    { name := "unit/n/negative" -- [B3]
      run := do
        expectErr "n-negative" (runDictSet dictSetSlice (mkSliceStack sampleSliceA (natToBits 5 8) .null (-1))) .rangeChk },
    { name := "unit/n/too-large" -- [B3]
      run := do
        expectErr "n-too-large" (runDictSet dictSetSlice (mkSliceStack sampleSliceA (natToBits 5 8) .null 1024)) .rangeChk },
    { name := "unit/dict/not-maybe-cell" -- [B4]
      run := do
        expectErr "dict-bad" (runDictSet dictSetSlice (mkSliceStack sampleSliceA (natToBits 5 8) (.tuple #[]) 8)) .typeChk },
    { name := "unit/key/not-slice-for-slice-branch" -- [B5]
      run := do
        expectErr "key-not-slice" (runDictSet dictSetSlice (mkIntStack (.slice sampleSliceA) 5 .null 8)) .typeChk },
    { name := "unit/key/not-int-for-int-branch" -- [B6]
      run := do
        expectErr "key-not-int" (runDictSet dictSetSigned (mkSliceStack sampleSliceA (natToBits 5 8) .null 8)) .typeChk },
    { name := "unit/value/not-slice-for-set-slice" -- [B7]
      run := do
        expectErr "value-not-slice" (runDictSet dictSetSlice (mkIntStack (.cell sampleCellA) 5 .null 8)) .typeChk },
    { name := "unit/value/not-cell-for-set-ref" -- [B8]
      run := do
        expectErr "value-not-cell" (runDictSet dictSetSliceRef (mkIntStack (.slice sampleSliceA) 5 .null 8)) .typeChk },
    { name := "unit/slice-key-too-short" -- [B5]
      run := do
        expectErr "slice-key-too-short" (runDictSet dictSetSlice (mkSliceStack sampleSliceA (natToBits 255 4) .null 8)) .cellUnd },
    { name := "unit/int-key-nan" -- [B6]
      run := do
        expectErr "int-key-nan" (runDictSet dictSetSigned #[.slice sampleSliceA, .int .nan, .null, intV 8]) .rangeChk },
    { name := "unit/int-key-range-signed" -- [B6]
      run := do
        expectErr "int-key-range-signed" (runDictSet dictSetSigned (mkIntStack (.slice sampleSliceA) (-129) .null 8)) .rangeChk },
    { name := "unit/int-key-range-unsigned" -- [B6]
      run := do
        expectErr "int-key-range-unsigned" (runDictSet dictSetUnsigned (mkIntStack (.slice sampleSliceA) (-1) .null 8)) .rangeChk },
    { name := "unit/set/slice-hit"
      run := do
        let expected := dictSetSliceExpected! (some dictSlice8) (natToBits 5 8) sampleSliceD .set
        expectOkStack "set/slice-hit" (runDictSet dictSetSlice (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8)) #[(.cell expected)] },
    { name := "unit/set/slice-miss-null"
      run := do
        let expected := dictSetSliceExpected! none (natToBits 9 8) sampleSliceD .set
        expectOkStack "set/slice-miss-null" (runDictSet dictSetSlice (mkSliceStack sampleSliceD (natToBits 9 8) .null 8)) #[(.cell expected)] },
    { name := "unit/set/ref-hit"
      run := do
        let expected := dictSetRefExpected! (some dictRef8Root) (natToBits 5 8) sampleCellD .set
        expectOkStack "set/ref-hit" (runDictSet dictSetSliceRef (mkRefStack sampleCellD (natToBits 5 8) (.cell dictRef8Root) 8)) #[(.cell expected)] },
    { name := "unit/set/replace-non-op-path" -- [B9]
      run := do
        expectOkStack "set/zero-bit" (runDictSet dictSetSlice (mkSliceStack sampleSliceE #[] (.cell dictSlice0Root) 0)) #[(.cell (dictSetSliceExpected! (some dictSlice0Root) #[] sampleSliceE .set))] },
    { name := "unit/replace/slice-hit"
      run := do
        let expected := dictSetSliceExpected! (some dictSlice8) (natToBits 5 8) sampleSliceD .replace
        expectOkStack "replace/slice-hit" (runDictSet dictReplaceSlice (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8)) #[(.cell expected), intV (-1)] },
    { name := "unit/replace/slice-miss"
      run := do
        expectOkStack "replace/slice-miss" (runDictSet dictReplaceSlice (mkSliceStack sampleSliceD (natToBits 10 8) (.cell dictSlice8) 8)) #[(.cell dictSlice8), intV 0] },
    { name := "unit/replace/signed-hit"
      run := do
        let expected := dictSetSliceIntExpected! (some dictInt8Signed) 8 false 6 sampleSliceD .replace
        expectOkStack "replace/signed-hit" (runDictSet dictReplaceSigned (mkIntStack (.slice sampleSliceD) 6 (.cell dictInt8Signed) 8)) #[(.cell expected), intV (-1)] },
    { name := "unit/replace/unsigned-miss"
      run := do
        expectOkStack "replace/unsigned-miss" (runDictSet dictReplaceUnsigned (mkIntStack (.slice sampleSliceD) 128 (.cell dictInt8Unsigned) 8)) #[(.cell dictInt8Unsigned), intV 0] },
    { name := "unit/add/slice-miss"
      run := do
        let expected := dictSetSliceExpected! none (natToBits 10 8) sampleSliceD .add
        expectOkStack "add/slice-miss" (runDictSet dictAddSlice (mkSliceStack sampleSliceD (natToBits 10 8) .null 8)) #[(.cell expected), intV (-1)] },
    { name := "unit/add/slice-hit"
      run := do
        let expected := dictSlice8
        expectOkStack "add/slice-hit" (runDictSet dictAddSlice (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8)) #[(.cell expected), intV 0] },
    { name := "unit/add/ref-hit"
      run := do
        expectOkStack "add/ref-hit" (runDictSet dictAddSliceRef (mkRefStack sampleCellD (natToBits 5 8) (.cell dictRef8Root) 8)) #[(.cell dictRef8Root), intV 0] },
    { name := "unit/add/ref-miss"
      run := do
        let expected := dictSetRefExpected! none (natToBits 10 8) sampleCellD .add
        expectOkStack "add/ref-miss" (runDictSet dictAddSliceRef (mkRefStack sampleCellD (natToBits 10 8) .null 8)) #[(.cell expected), intV (-1)] },
    { name := "unit/replace-malformed-root"
      run := do
        expectErr "replace-malformed" (runDictSet dictReplaceSlice (mkSliceStack sampleSliceA (natToBits 5 8) (.cell malformedDictCell) 8)) .dictErr },
    { name := "unit/asm/encode/set"
      run := do
        expectAssembleEq "asm/set/0" raw412 dictSetSlice
        expectAssembleEq "asm/set/1" raw413 dictSetSliceRef
        expectAssembleEq "asm/set/2" raw414 dictSetSigned
        expectAssembleEq "asm/set/3" raw415 dictSetSignedRef
        expectAssembleEq "asm/set/4" raw416 dictSetUnsigned
        expectAssembleEq "asm/set/5" raw417 dictSetUnsignedRef },
    { name := "unit/asm/encode/replace"
      run := do
        expectAssembleEq "asm/replace/0" raw422 dictReplaceSlice
        expectAssembleEq "asm/replace/1" raw423 dictReplaceSliceRef
        expectAssembleEq "asm/replace/2" raw424 dictReplaceSigned
        expectAssembleEq "asm/replace/3" raw425 dictReplaceSignedRef
        expectAssembleEq "asm/replace/4" raw426 dictReplaceUnsigned
        expectAssembleEq "asm/replace/5" raw427 dictReplaceUnsignedRef },
    { name := "unit/asm/encode/add"
      run := do
        expectAssembleEq "asm/add/0" raw432 dictAddSlice
        expectAssembleEq "asm/add/1" raw433 dictAddSliceRef
        expectAssembleEq "asm/add/2" raw434 dictAddSigned
        expectAssembleEq "asm/add/3" raw435 dictAddSignedRef
        expectAssembleEq "asm/add/4" raw436 dictAddUnsigned
        expectAssembleEq "asm/add/5" raw437 dictAddUnsignedRef
        expectAssembleInv "asm/invalid/signed-non-int/.set" (.dictSet false true false .set)
        expectAssembleInv "asm/invalid/signed-non-int/.replace" (.dictSet false true false .replace)
        expectAssembleInv "asm/invalid/signed-non-int/.add" (.dictSet false true false .add) },
    { name := "unit/decode/valid"
      run := do
        expectDecodeEq "decode/412" 0xF412 dictSetSlice
        expectDecodeEq "decode/415" 0xF415 dictSetSignedRef
        expectDecodeEq "decode/422" 0xF422 dictReplaceSlice
        expectDecodeEq "decode/424" 0xF424 dictReplaceSigned
        expectDecodeEq "decode/432" 0xF432 dictAddSlice
        expectDecodeEq "decode/436" 0xF436 dictAddUnsigned },
    { name := "unit/decode/invalid-boundaries"
      run := do
        expectDecodeInv "decode/411" raw421
        expectDecodeInv "decode/418" raw418
        expectDecodeInv "decode/421" raw421
        expectDecodeInv "decode/428" raw428
        expectDecodeInv "decode/431" raw431
        expectDecodeInv "decode/438" raw438
        expectDecodeInv "decode/truncated-8bit" rawF4 },
    { name := "unit/gas/set-slice-exact"
      run := do
        expectOkStack "set/slice-exact" (runDictSet dictSetSlice (mkSliceStack sampleSliceD (natToBits 10 8) .null 8)) #[(.cell (dictSetSliceExpected! none (natToBits 10 8) sampleSliceD .set))]
    }
  ]
  oracle := #[
    mkCase "oracle/underflow-empty" #[] -- [B2]
    , mkCase "oracle/underflow-one" #[.slice sampleSliceA] -- [B2]
    , mkCase "oracle/underflow-two" #[.slice sampleSliceA, .int (.num 5)] -- [B2]
  , mkCase "oracle/underflow-three" #[.slice sampleSliceA, .int (.num 5), .null] -- [B2]
    , mkCase "oracle/n-negative" (mkSliceStack sampleSliceA (natToBits 5 8) .null (-1)) -- [B3]
    , mkCase "oracle/n-too-large" (mkSliceStack sampleSliceA (natToBits 5 8) .null 1024) -- [B3]
    , mkCase "oracle/n-nan" #[.slice sampleSliceA, .slice (mkSliceFromBits (natToBits 5 8)), .null, .int .nan] -- [B3]
    , mkCase "oracle/type-dict" (mkSliceStack sampleSliceA (natToBits 5 8) (.tuple #[]) 8) -- [B4]
    , mkCase "oracle/key-type-slice" (mkIntStack (.slice sampleSliceA) 5 (.cell dictSlice8) 8) -- [B5]
    , mkCase "oracle/key-type-int" (mkSliceStack sampleSliceA (natToBits 5 8) (.cell dictInt8Signed) 8) (#[dictSetSigned]) -- [B6]
    , mkCase "oracle/value-type-slice" (mkIntStack (.cell sampleCellA) 5 (.cell dictInt8Signed) 8) (#[dictSetSigned]) -- [B7]
    , mkCase "oracle/value-type-ref" (mkIntStack (.slice sampleSliceA) 5 (.cell dictInt8SignedRef) 8) (#[dictSetSignedRef]) -- [B8]
    , mkCase "oracle/slice-key-too-short" (mkSliceStack sampleSliceA (natToBits 5 3) (.cell dictSlice8) 8) -- [B5]
    , mkCase "oracle/int-key-oob-signed-high" (mkIntStack (.slice sampleSliceA) 128 (.cell dictInt8Signed) 8) (#[dictSetSigned]) -- [B6]
    , mkCase "oracle/int-key-oob-signed-low" (mkIntStack (.slice sampleSliceA) (-129) (.cell dictInt8Signed) 8) (#[dictSetSigned]) -- [B6]
    , mkCase "oracle/int-key-oob-unsigned-high" (mkIntStack (.slice sampleSliceA) 256 (.cell dictInt8Unsigned) 8) (#[dictSetUnsigned]) -- [B6]
    , mkCase "oracle/int-key-oob-unsigned-neg" (mkIntStack (.slice sampleSliceA) (-1) (.cell dictInt8Unsigned) 8) (#[dictSetUnsigned]) -- [B6]
    , mkCase "oracle/set-slice-hit" (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8) (#[dictSetSlice]) -- [B7][B9]
    , mkCase "oracle/set-slice-miss" (mkSliceStack sampleSliceD (natToBits 10 8) .null 8) (#[dictSetSlice]) -- [B9]
    , mkCase "oracle/set-ref-hit" (mkRefStack sampleCellD (natToBits 5 8) (.cell dictRef8Root) 8) (#[dictSetSliceRef]) -- [B7][B9]
    , mkCase "oracle/set-ref-miss" (mkRefStack sampleCellD (natToBits 10 8) .null 8) (#[dictSetSliceRef]) -- [B9]
    , mkCase "oracle/set-signed-hit" (mkIntStack (.slice sampleSliceE) 6 (.cell dictInt8Signed) 8) (#[dictSetSigned]) -- [B6][B9]
    , mkCase "oracle/set-unsigned-hit" (mkIntStack (.slice sampleSliceE) 7 (.cell dictInt8Unsigned) 8) (#[dictSetUnsigned]) -- [B6][B9]
    , mkCase "oracle/replace-slice-hit" (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8) (#[dictReplaceSlice]) -- [B10]
    , mkCase "oracle/replace-slice-miss" (mkSliceStack sampleSliceD (natToBits 10 8) (.cell dictSlice8) 8) (#[dictReplaceSlice]) -- [B10]
    , mkCase "oracle/replace-signed-hit" (mkIntStack (.slice sampleSliceD) 6 (.cell dictInt8Signed) 8) (#[dictReplaceSigned]) -- [B10]
    , mkCase "oracle/replace-unsigned-hit" (mkIntStack (.slice sampleSliceD) 7 (.cell dictInt8Unsigned) 8) (#[dictReplaceUnsigned]) -- [B10]
    , mkCase "oracle/replace-unsigned-miss" (mkIntStack (.slice sampleSliceD) 12 (.cell dictInt8Unsigned) 8) (#[dictReplaceUnsigned]) -- [B10]
    , mkCase "oracle/add-slice-miss" (mkSliceStack sampleSliceD (natToBits 10 8) .null 8) (#[dictAddSlice]) -- [B11]
    , mkCase "oracle/add-slice-hit" (mkSliceStack sampleSliceD (natToBits 5 8) (.cell dictSlice8) 8) (#[dictAddSlice]) -- [B11]
    , mkCase "oracle/add-ref-miss" (mkRefStack sampleCellD (natToBits 10 8) .null 8) (#[dictAddSliceRef]) -- [B11]
    , mkCase "oracle/add-ref-hit" (mkRefStack sampleCellD (natToBits 5 8) (.cell dictRef8Root) 8) (#[dictAddSliceRef]) -- [B11]
    , mkCase "oracle/add-signed-hit" (mkIntStack (.slice sampleSliceE) 6 (.cell dictInt8Signed) 8) (#[dictAddSigned]) -- [B11]
    , mkCase "oracle/add-unsigned-hit" (mkIntStack (.slice sampleSliceE) 7 (.cell dictInt8Unsigned) 8) (#[dictAddUnsigned]) -- [B11]
    , mkCase "oracle/malformed-root-slice" (mkSliceStack sampleSliceA (natToBits 5 8) (.cell malformedDictCell) 8) (#[dictSetSlice]) -- [B12]
    , mkCase "oracle/malformed-root-ref" (mkRefStack sampleCellA (natToBits 5 8) (.cell malformedDictCell) 8) (#[dictSetSliceRef]) -- [B12]
    , mkCase "oracle/asmdetect" #[] (#[dictSetSlice]) -- [B13]
    , mkCodeCase "oracle/decode/412" #[] raw412 -- [B14]
    , mkCodeCase "oracle/decode/417" #[] raw417 -- [B14]
    , mkCodeCase "oracle/decode/422" #[] raw422 -- [B14]
    , mkCodeCase "oracle/decode/427" #[] raw427 -- [B14]
    , mkCodeCase "oracle/decode/436" #[] raw436 -- [B14]
    , mkCodeCase "oracle/decode/437" #[] raw437 -- [B14]
    , mkCodeCase "oracle/decode/411-invalid" #[] raw421 -- [B14]
    , mkCodeCase "oracle/decode/418-invalid" #[] raw418 -- [B14]
    , mkCodeCase "oracle/decode/428-invalid" #[] raw428 -- [B14]
    , mkCodeCase "oracle/decode/431-invalid" #[] (Cell.mkOrdinary (natToBits 0xF431 16) #[]) -- [B14]
    , mkCodeCase "oracle/decode/438-invalid" #[] raw438 -- [B14]
    , mkCodeCase "oracle/decode/truncated-8bit" #[] rawF4 -- [B14]
    , mkCase "oracle/gas/set/exact" (mkSliceStack sampleSliceD (natToBits 10 8) .null 8) (mkGasProgram setSliceGas dictSetSlice) (oracleGasLimitsExact setSliceGas) -- [B15]
    , mkCase "oracle/gas/set/minus-one" (mkSliceStack sampleSliceD (natToBits 10 8) .null 8) (mkGasProgram setSliceGasMinusOne dictSetSlice) (oracleGasLimitsExactMinusOne setSliceGasMinusOne) -- [B15]
    , mkCase "oracle/gas/replace-hit/exact" (mkIntStack (.slice sampleSliceD) 6 (.cell dictInt8Signed) 8) (mkGasProgram replaceSignedHitGas dictReplaceSigned) (oracleGasLimitsExact replaceSignedHitGas) -- [B15]
    , mkCase "oracle/gas/replace-hit/minus-one" (mkIntStack (.slice sampleSliceD) 6 (.cell dictInt8Signed) 8) (mkGasProgram replaceSignedHitGasMinusOne dictReplaceSigned) (oracleGasLimitsExactMinusOne replaceSignedHitGasMinusOne) -- [B15]
    , mkCase "oracle/gas/replace-miss/minus-one" (mkIntStack (.slice sampleSliceD) 128 (.cell dictInt8Signed) 8) (mkGasProgram replaceSliceMissGasMinusOne dictReplaceSigned) (oracleGasLimitsExactMinusOne replaceSliceMissGasMinusOne) -- [B15]
    , mkCase "oracle/gas/add-miss/exact" (mkSliceStack sampleSliceD (natToBits 10 8) .null 8) (mkGasProgram addSliceGas dictAddSlice) (oracleGasLimitsExact addSliceGas) -- [B15]
    , mkCase "oracle/gas/add-miss/minus-one" (mkSliceStack sampleSliceD (natToBits 10 8) .null 8) (mkGasProgram addSliceGasMinusOne dictAddSlice) (oracleGasLimitsExactMinusOne addSliceGasMinusOne) -- [B15]
    , mkCase "oracle/gas/add-unsigned-exact" (mkIntStack (.slice sampleSliceD) 11 (.null) 8) (mkGasProgram addUnsignedGas dictAddUnsigned) (oracleGasLimitsExact addUnsignedGas) -- [B15]
    , mkCase "oracle/gas/add-unsigned-minus" (mkIntStack (.slice sampleSliceD) 11 (.null) 8) (mkGasProgram addUnsignedGasMinusOne dictAddUnsigned) (oracleGasLimitsExactMinusOne addUnsignedGasMinusOne) -- [B15]
    , mkCase "oracle/zero-width-set" (mkSliceStack sampleSliceE #[] .null 0) -- [B5][B9]
    , mkCase "oracle/zero-width-replace" (mkSliceStack sampleSliceE #[] (.cell dictSlice0Root) 0) (#[dictReplaceSlice]) -- [B10]
  ]
  fuzz := #[
    {
      seed := fuzzSeed
      count := 500
      gen := genDICTSETFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTSET
