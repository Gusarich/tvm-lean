import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREPLACEGETB

/-
INSTRUCTION: DICTIREPLACEGETB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path:
   `execInstrDictExt` dispatches to `.dictExt (.mutGetB _ _ .replace)` only when opcode family matches;
   otherwise it returns `next`.
2. [B2] Stack-underflow check:
   every valid execution path enforces `VM.checkUnderflow 4`.
3. [B3] Slice-key runtime branch:
   pops slice key, requires at least `n` bits; otherwise `.cellUnd`.
4. [B4] Signed integer key runtime branch:
   `int` key converted by `dictKeyBits?` with `unsigned = false`; NaN/out-of-range raises `.rangeChk`.
5. [B5] Unsigned integer key runtime branch:
   `int` key converted by `dictKeyBits?` with `unsigned = true`; negative/out-of-range raises `.rangeChk`.
6. [B6] Hit/miss behavior:
   `.replace` always pushes new root. Hit returns old value slice + `-1`; miss returns `null + 0`.
7. [B7] Structural errors:
   malformed dictionary traversal may raise `.dictErr` (with loaded-cell accounting).
8. [B8] Assembler branch:
   `.dictExt (.mutGetB .. .replace)` assembles for slice/signed/unsigned variants.
9. [B9] Decoder boundaries:
   decodes only `0xf44d`, `0xf44e`, `0xf44f` for replace-get builder:
   bit1 selects integer key; bit0 then selects unsigned for integer mode.
10. [B10] Decode neighbor behavior:
   adjacent opcodes (`0xf44c`, `0xf450`, and truncated 8-bit input) are invalid.
11. [B11] Gas behavior:
   exact budget must pass, exact-1 must fail; hit paths include optional `created * cellCreateGasPrice` term.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests should be covered by the fuzzer.
-/

private def suiteId : InstrId := { name := "DICTIREPLACEGETB" }

private def instrSlice : Instr := .dictExt (.mutGetB false false .replace)
private def instrSigned : Instr := .dictExt (.mutGetB true false .replace)
private def instrSignedUnsigned : Instr := .dictExt (.mutGetB true true .replace)

private def rawF44D : Cell := Cell.mkOrdinary (natToBits 0xF44D 16) #[]
private def rawF44E : Cell := Cell.mkOrdinary (natToBits 0xF44E 16) #[]
private def rawF44F : Cell := Cell.mkOrdinary (natToBits 0xF44F 16) #[]
private def rawF44C : Cell := Cell.mkOrdinary (natToBits 0xF44C 16) #[]
private def rawF450 : Cell := Cell.mkOrdinary (natToBits 0xF450 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def valueA : Builder := Builder.empty.storeBits (natToBits 0xA1 8)
private def valueB : Builder := Builder.empty.storeBits (natToBits 0xB2 8)
private def valueC : Builder := Builder.empty.storeBits (natToBits 0xC3 8)
private def valueD : Builder := Builder.empty.storeBits (natToBits 0xD4 8)
private def valueE : Builder := Builder.empty.storeBits (natToBits 0xE5 8)
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkDictInt! (label : String) (n : Nat) (unsigned : Bool)
    (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in pairs do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n unsigned with
        | some bs => bs
        | none =>
            panic! s!"DICTIREPLACEGETB: {label}: out-of-range int key k={k}, n={n}, unsigned={unsigned}"
      match dictSetBuilderWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"DICTIREPLACEGETB: {label}: unexpected empty root during set"
      | .error e =>
          panic! s!"DICTIREPLACEGETB: {label}: dict set failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"DICTIREPLACEGETB: {label}: dictionary construction produced no root"

private def mkDictBits! (label : String) (pairs : Array (BitString × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in pairs do
      let (k, v) := entry
      match dictSetBuilderWithCells root k v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"DICTIREPLACEGETB: {label}: unexpected empty root during set"
      | .error e =>
          panic! s!"DICTIREPLACEGETB: {label}: dict set failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"DICTIREPLACEGETB: {label}: dictionary construction produced no root"

private def dictSigned0 : Cell :=
  mkDictInt! "dictSigned0" 0 false #[(0, valueA)]

private def dictSigned4 : Cell :=
  mkDictInt! "dictSigned4" 4 false #[
    (-8, valueA),
    (-1, valueB),
    (0, valueC),
    (7, valueD)
  ]

private def dictSigned8 : Cell :=
  mkDictInt! "dictSigned8" 8 false #[
    (-128, valueA),
    (-1, valueB),
    (0, valueC),
    (42, valueD),
    (127, valueE)
  ]

private def dictUnsigned8 : Cell :=
  mkDictInt! "dictUnsigned8" 8 true #[
    (0, valueA),
    (1, valueB),
    (64, valueC),
    (255, valueD)
  ]

private def dictSlice8 : Cell :=
  mkDictBits! "dictSlice8" #[
    (natToBits 0 8, valueA),
    (natToBits 5 8, valueB),
    (natToBits 42 8, valueC),
    (natToBits 255 8, valueD)
  ]

private def dictSlice4 : Cell :=
  mkDictBits! "dictSlice4" #[
    (natToBits 0 4, valueA),
    (natToBits 6 4, valueB)
  ]

private def slice8A : Slice := mkSliceFromBits (natToBits 0 8)
private def slice8B : Slice := mkSliceFromBits (natToBits 5 8)
private def slice8C : Slice := mkSliceFromBits (natToBits 42 8)
private def slice8Miss : Slice := mkSliceFromBits (natToBits 170 8)
private def slice4A : Slice := mkSliceFromBits (natToBits 1 4)
private def slice4Miss : Slice := mkSliceFromBits (natToBits 3 4)
private def slice8Short : Slice := mkSliceFromBits (natToBits 5 3)
private def slice4Short : Slice := mkSliceFromBits (natToBits 1 1)
private def sliceZero : Slice := mkSliceFromBits #[]

private def mkIntStack
    (n : Int)
    (key : Int)
    (dict : Value := .null)
    (value : Builder := valueA) : Array Value :=
  #[.builder value, intV key, dict, intV n]

private def mkSliceStack
    (n : Int)
    (key : Slice)
    (dict : Value := .null)
    (value : Builder := valueA) : Array Value :=
  #[.builder value, .slice key, dict, intV n]

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

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (instr : Instr)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack
    (#[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr])
    gasLimits
    fuel

private def expectAssembleErr
    (label : String)
    (expected : Excno)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure {expected}, got success")

private def expectAssembleOk16 (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok out => do
      let rest ← expectDecodeStep label (Slice.ofCell out) instr 16
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected no trailing bits")
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")

private def expectDecodeInv (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr} with {bits} bits")

private def createdBits (root : Cell) (bits : BitString) (value : Builder) : Nat :=
  match dictLookupSetBuilderWithCells (some root) bits value .replace with
  | .ok (_, _, _ok, created, _loaded) =>
      created
  | .error _ =>
      0

private def createdInt
    (root : Cell)
    (n : Nat)
    (unsigned : Bool)
    (key : Int)
    (value : Builder) : Nat :=
  match dictKeyBits? key n unsigned with
  | none => 0
  | some bits => createdBits root bits value

private def replaceBaseGasSlice : Int := computeExactGasBudget instrSlice
private def replaceBaseGasSigned : Int := computeExactGasBudget instrSigned
private def replaceBaseGasUnsigned : Int := computeExactGasBudget instrSignedUnsigned

private def replaceMissGas : Int := replaceBaseGasSigned
private def replaceMissGasMinusOne : Int := computeExactGasBudgetMinusOne instrSigned

private def replaceSliceCreated : Nat := createdBits dictSlice8 (natToBits 42 8) valueA
private def replaceSignedCreated : Nat := createdInt dictSigned8 8 false 42 valueA
private def replaceUnsignedCreated : Nat := createdInt dictUnsigned8 8 true 255 valueA

private def replaceSliceGas : Int :=
  replaceBaseGasSlice + Int.ofNat replaceSliceCreated * cellCreateGasPrice
private def replaceSignedGas : Int :=
  replaceBaseGasSigned + Int.ofNat replaceSignedCreated * cellCreateGasPrice
private def replaceUnsignedGas : Int :=
  replaceBaseGasUnsigned + Int.ofNat replaceUnsignedCreated * cellCreateGasPrice

private def replaceSliceGasMinusOne : Int :=
  if replaceSliceGas > 0 then replaceSliceGas - 1 else 0
private def replaceSignedGasMinusOne : Int :=
  if replaceSignedGas > 0 then replaceSignedGas - 1 else 0
private def replaceUnsignedGasMinusOne : Int :=
  if replaceUnsignedGas > 0 then replaceUnsignedGas - 1 else 0

private def runDICTIREPLACEGETBFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (.int (.num 777))) stack

private def runDICTIREPLACEGETBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def genDICTIREPLACEGETBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 16 then
    let (idx, rng2) := randNat rng1 0 3
    let c : OracleCase :=
      if idx = 0 then
        mkCase "fuzz/underflow/empty" #[]
      else if idx = 1 then
        mkCase "fuzz/underflow/one" #[.builder valueA]
      else if idx = 2 then
        mkCase "fuzz/underflow/two" #[.builder valueA, intV 1]
      else
        mkCase "fuzz/underflow/three" #[.builder valueA, .slice slice8A, .cell dictSlice8]
    (c, rng2)
  else if shape < 32 then
    let (sel, rng2) := randNat rng1 0 4
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/signed-hit/4/-8" (mkIntStack 4 (-8) (.cell dictSigned4) valueB)
      else if sel = 1 then
        mkCase "fuzz/signed-hit/4/7" (mkIntStack 4 7 (.cell dictSigned4) valueC)
      else if sel = 2 then
        mkCase "fuzz/signed-hit/8/42" (mkIntStack 8 42 (.cell dictSigned8) valueA)
      else if sel = 3 then
        mkCase "fuzz/unsigned-hit/8/0" (mkIntStack 8 0 (.cell dictUnsigned8) valueB) #[instrSignedUnsigned]
      else
        mkCase "fuzz/unsigned-hit/8/255" (mkIntStack 8 255 (.cell dictUnsigned8) valueC) #[instrSignedUnsigned]
    (c, rng2)
  else if shape < 44 then
    let (sel, rng2) := randBool rng1
    let c : OracleCase :=
      if sel then
        mkCase "fuzz/signed-miss/nonempty" (mkIntStack 4 6 (.cell dictSigned4) valueA)
      else
        mkCase "fuzz/signed-miss/null" (mkIntStack 8 13 .null valueA)
    (c, rng2)
  else if shape < 56 then
    let (sel, rng2) := randNat rng1 0 2
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/slice-hit" (mkSliceStack 8 slice8C (.cell dictSlice8) valueA) #[instrSlice]
      else if sel = 1 then
        mkCase "fuzz/slice-miss" (mkSliceStack 8 slice8Miss (.cell dictSlice8) valueA) #[instrSlice]
      else
        mkCase "fuzz/slice-cellund" (mkSliceStack 8 slice8Short (.cell dictSlice8) valueA) #[instrSlice]
    (c, rng2)
  else if shape < 70 then
    let (sel, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/range/n-negative" (mkIntStack (-1) 0 (.cell dictSigned8) valueA)
      else if sel = 1 then
        mkCase "fuzz/range/n-too-large" (mkIntStack 1024 0 (.cell dictSigned8) valueA)
      else if sel = 2 then
        mkCase "fuzz/type/nan" (#[.builder valueA, intV 1, .cell dictSigned8, .int .nan])
      else if sel = 3 then
        mkCase "fuzz/range/int-key-high" (mkIntStack 4 8 (.cell dictSigned4) valueA)
      else if sel = 4 then
        mkCase "fuzz/range/int-key-low" (mkIntStack 4 (-9) (.cell dictSigned4) valueA)
      else
        mkCase "fuzz/range/unsigned-high" (mkIntStack 8 (-1) (.cell dictUnsigned8) valueA) #[instrSignedUnsigned]
    (c, rng2)
  else if shape < 84 then
    let (sel, rng2) := randNat rng1 0 4
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/type/value-not-builder" (#[ .int (.num 7), intV 1, .cell dictSigned4, intV 4 ])
      else if sel = 1 then
        mkCase "fuzz/type/key-not-int" (#[.builder valueA, .slice slice8A, .cell dictSigned8, intV 8])
      else if sel = 2 then
        mkCase "fuzz/type/dict-not-maybe-cell" (mkIntStack 4 0 (.tuple #[]))
      else if sel = 3 then
        mkCase "fuzz/type/malformed-int-root" (mkIntStack 8 1 (.cell malformedDict) valueA)
      else
        mkCase "fuzz/type/malformed-slice-root" (mkSliceStack 8 slice8A (.cell malformedDict) valueA) #[instrSlice]
    (c, rng2)
  else
    let (sel, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkGasCase "fuzz/gas/signed-miss-exact" (mkIntStack 0 1 .null) instrSigned replaceMissGas (oracleGasLimitsExact replaceMissGas)
      else if sel = 1 then
        mkGasCase "fuzz/gas/signed-miss-exact-minus-one" (mkIntStack 0 1 .null) instrSigned replaceMissGasMinusOne (oracleGasLimitsExactMinusOne replaceMissGas)
      else if sel = 2 then
        mkGasCase "fuzz/gas/slice-hit-exact" (mkSliceStack 8 slice8C (.cell dictSlice8) valueA) instrSlice replaceSliceGas (oracleGasLimitsExact replaceSliceGas)
      else if sel = 3 then
        mkGasCase "fuzz/gas/slice-hit-exact-minus-one" (mkSliceStack 8 slice8C (.cell dictSlice8) valueA) instrSlice replaceSliceGasMinusOne (oracleGasLimitsExactMinusOne replaceSliceGas)
      else if sel = 4 then
        mkGasCase "fuzz/gas/signed-hit-exact" (mkIntStack 8 42 (.cell dictSigned8) valueA) instrSigned replaceSignedGas (oracleGasLimitsExact replaceSignedGas)
      else
        mkGasCase "fuzz/gas/unsigned-hit-exact" (mkIntStack 8 255 (.cell dictUnsigned8) valueA) instrSignedUnsigned replaceUnsignedGas (oracleGasLimitsExact replaceUnsignedGas)
    (c, rng2)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let expected := mkIntStack 4 1 (.cell dictSigned4) valueA ++ #[.int (.num 777)]
        expectOkStack "fallback" (runDICTIREPLACEGETBFallback (mkIntStack 4 1 (.cell dictSigned4) valueA)) expected },
    { name := "unit/asm/encodes" -- [B8]
      run := do
        expectAssembleOk16 "assemble/slice" instrSlice
        expectAssembleOk16 "assemble/signed" instrSigned
        expectAssembleOk16 "assemble/unsigned" instrSignedUnsigned },
    { name := "unit/decode/valid" -- [B9]
      run := do
        let _ ← expectDecodeStep "decode/f44d" (Slice.ofCell rawF44D) instrSlice 16
        let _ ← expectDecodeStep "decode/f44e" (Slice.ofCell rawF44E) instrSigned 16
        let _ ← expectDecodeStep "decode/f44f" (Slice.ofCell rawF44F) instrSignedUnsigned 16 },
    { name := "unit/decode/invalid-adjacent-and-truncated" -- [B10]
      run := do
        expectDecodeInv "decode/f44c-invalid" rawF44C
        expectDecodeInv "decode/f450-invalid" rawF450
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode") },
    { name := "unit/runtime/validation" -- [B2][B6][B7]
      run := do
        expectErr "underflow" (runDICTIREPLACEGETBDirect instrSlice #[]) .stkUnd
        expectErr "n-negative" (runDICTIREPLACEGETBDirect instrSlice (mkIntStack (-1) 1 (.cell dictSigned8) valueA)) .rangeChk
        expectErr "n-too-large" (runDICTIREPLACEGETBDirect instrSlice (mkIntStack 1024 1 (.cell dictSigned8) valueA)) .rangeChk
        expectErr "n-nan" (runDICTIREPLACEGETBDirect instrSlice (#[ .builder valueA, intV 1, .cell dictSigned8, .int .nan ])) .rangeChk
        expectErr "key-short" (runDICTIREPLACEGETBDirect instrSlice (mkSliceStack 8 slice8Short (.cell dictSlice8) valueA)) .cellUnd
        expectErr "type-top" (runDICTIREPLACEGETBDirect instrSlice (#[.int (.num 7), intV 1, .cell dictSigned8, intV 8])) .typeChk
        expectErr "type-key" (runDICTIREPLACEGETBDirect instrSigned (#[.builder valueA, .slice slice8A, .cell dictSigned8, intV 8])) .typeChk
        expectErr "type-dict" (runDICTIREPLACEGETBDirect instrSlice (mkIntStack 4 1 (.tuple #[]) valueA)) .typeChk
        match runDICTIREPLACEGETBDirect instrSigned (mkIntStack 8 1 (.cell malformedDict) valueA) with
        | .error .dictErr => pure ()
        | .error .cellUnd => pure ()
        | .error e =>
            throw (IO.userError s!"dict-err: expected dictErr/cellUnd, got {e}")
        | .ok st =>
            throw (IO.userError s!"dict-err: expected failure, got {reprStr st}")
      } ]
  oracle := #[
    -- [B2] slice hits and misses
    mkCase "ok/slice-hit/8" (mkSliceStack 8 slice8C (.cell dictSlice8) valueA) #[instrSlice], -- [B2] [B6]
    mkCase "ok/slice-hit/4" (mkSliceStack 4 slice4A (.cell dictSlice4) valueA) #[instrSlice], -- [B2] [B6]
    mkCase "ok/slice-hit-zero" (mkSliceStack 0 sliceZero (.cell dictSlice8) valueA) #[instrSlice], -- [B2] [B6]
    mkCase "ok/slice-miss/8" (mkSliceStack 8 slice8Miss (.cell dictSlice8) valueA) #[instrSlice], -- [B6]
    mkCase "ok/slice-miss/4" (mkSliceStack 4 slice4Miss (.cell dictSlice4) valueA) #[instrSlice], -- [B6]

    -- [B3] signed path hits/misses
    mkCase "ok/signed-hit/0" (mkIntStack 0 0 (.cell dictSigned0) valueA), -- [B3] [B6]
    mkCase "ok/signed-hit/4/min" (mkIntStack 4 (-8) (.cell dictSigned4) valueA), -- [B3] [B6]
    mkCase "ok/signed-hit/4/max" (mkIntStack 4 7 (.cell dictSigned4) valueA), -- [B3] [B6]
    mkCase "ok/signed-hit/8/127" (mkIntStack 8 127 (.cell dictSigned8) valueA), -- [B3] [B6]
    mkCase "ok/signed-hit/8/miss" (mkIntStack 8 13 .null valueA), -- [B6]
    mkCase "ok/signed-miss/nonempty" (mkIntStack 4 6 (.cell dictSigned4) valueB), -- [B6]

    -- [B4] unsigned path hits/misses
    mkCase "ok/unsigned-hit/255" (mkIntStack 8 255 (.cell dictUnsigned8) valueA) #[instrSignedUnsigned], -- [B4]
    mkCase "ok/unsigned-hit/1" (mkIntStack 8 1 (.cell dictUnsigned8) valueA) #[instrSignedUnsigned], -- [B4]
    mkCase "ok/unsigned-miss" (mkIntStack 8 2 (.cell dictUnsigned8) valueA) #[instrSignedUnsigned], -- [B6]
    mkCase "ok/unsigned-miss/null" (mkIntStack 8 5 .null valueA) #[instrSignedUnsigned], -- [B6]

    -- [B5] underflow
    mkCase "err/underflow/empty" #[], -- [B5]
    mkCase "err/underflow/one" #[.builder valueA], -- [B5]
    mkCase "err/underflow/two" (mkIntStack 4 1 .null), -- [B5]
    mkCase "err/underflow/three" (mkSliceStack 8 slice8A .null), -- [B5]

    -- [B6] integer validation
    mkCase "err/nan-key/signed" (#[.builder valueA, .slice slice8A, .cell dictSigned8, intV 8]), -- [B6]
    mkCase "err/key-nan/signed" (#[.builder valueA, .int .nan, .cell dictSigned8, intV 8]), -- [B6]
    mkCase "err/key-out-of-range/signed-high" (mkIntStack 4 8 (.cell dictSigned4) valueA), -- [B6]
    mkCase "err/key-out-of-range/signed-low" (mkIntStack 4 (-9) (.cell dictSigned4) valueA), -- [B6]
    mkCase "err/key-out-of-range/unsigned" (mkIntStack 8 (-1) (.cell dictUnsigned8) valueA) #[instrSignedUnsigned], -- [B6]
    mkCase "err/key-out-of-range/unsigned-high" (mkIntStack 8 256 (.cell dictUnsigned8) valueA) #[instrSignedUnsigned], -- [B6]
    mkCase "err/range/n-negative" (mkIntStack (-1) 0 (.cell dictSigned8) valueA), -- [B6]
    mkCase "err/range/n-too-large" (mkIntStack 1024 0 (.cell dictSigned8) valueA), -- [B6]

    -- [B7] slice key too short
    mkCase "err/slice-short/8" (mkSliceStack 8 slice8Short (.cell dictSlice8) valueA) #[instrSlice], -- [B7]
    mkCase "err/slice-short/4" (mkSliceStack 4 slice4Short (.cell dictSlice4) valueA) #[instrSlice], -- [B7]

    -- [B8] malformed dictionary
    mkCase "err/dict-malformed/signed" (mkIntStack 8 1 (.cell malformedDict) valueA), -- [B7]
    mkCase "err/dict-malformed/slice" (mkSliceStack 8 slice8A (.cell malformedDict) valueA) #[instrSlice], -- [B8]
    mkCase "err/type/value-not-builder" (#[ .int (.num 7), intV 1, .cell dictSigned8, intV 8 ]), -- [B6]

    -- [B9][B10] decode via raw code cells
    mkCodeCase "ok/code/f44d" (mkSliceStack 8 slice8A (.cell dictSlice8) valueA) rawF44D, -- [B9]
    mkCodeCase "ok/code/f44e" (mkIntStack 8 42 (.cell dictSigned8) valueA) rawF44E, -- [B9]
    mkCodeCase "ok/code/f44f" (mkIntStack 8 255 (.cell dictUnsigned8) valueA) rawF44F, -- [B9]

    -- [B11] gas exactness and minus-one
    mkGasCase "gas/signed-miss-exact" (mkIntStack 0 1 .null) instrSigned replaceMissGas (oracleGasLimitsExact replaceMissGas),
    mkGasCase "gas/signed-miss-exact-minus-one" (mkIntStack 0 1 .null) instrSigned replaceMissGasMinusOne (oracleGasLimitsExactMinusOne replaceMissGas),
    mkGasCase "gas/slice-hit-exact" (mkSliceStack 8 slice8C (.cell dictSlice8) valueA) instrSlice replaceSliceGas (oracleGasLimitsExact replaceSliceGas),
    mkGasCase "gas/slice-hit-exact-minus-one" (mkSliceStack 8 slice8C (.cell dictSlice8) valueA) instrSlice (replaceSliceGasMinusOne) (oracleGasLimitsExactMinusOne replaceSliceGas),
    mkGasCase "gas/signed-hit-exact" (mkIntStack 8 42 (.cell dictSigned8) valueA) instrSigned replaceSignedGas (oracleGasLimitsExact replaceSignedGas),
    mkGasCase "gas/signed-hit-exact-minus-one" (mkIntStack 8 42 (.cell dictSigned8) valueA) instrSigned (replaceSignedGasMinusOne) (oracleGasLimitsExactMinusOne replaceSignedGas),
    mkGasCase "gas/unsigned-hit-exact" (mkIntStack 8 255 (.cell dictUnsigned8) valueA) instrSignedUnsigned replaceUnsignedGas (oracleGasLimitsExact replaceUnsignedGas),
    mkGasCase "gas/unsigned-hit-exact-minus-one" (mkIntStack 8 255 (.cell dictUnsigned8) valueA) instrSignedUnsigned (replaceUnsignedGasMinusOne) (oracleGasLimitsExactMinusOne replaceUnsignedGas)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTIREPLACEGETBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREPLACEGETB
