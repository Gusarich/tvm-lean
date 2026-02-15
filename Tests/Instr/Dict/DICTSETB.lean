import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTSETB

/-!
INSTRUCTION: DICTSETB

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `execInstrDictDictSetB` handles only `.dictSetB`.
   - Any non-`dictSetB` instruction must be delegated to `next`.

2. [B2] Runtime preamble and `n` validation.
   - `checkUnderflow 4` runs before any pops.
   - `popNatUpTo 1023` validates width; invalid widths produce `.rangeChk`.

3. [B3] Integer key conversion path.
   - For `intKey=true`, `popInt` then `dictKeyBits?`.
   - Signed mode uses signed two's complement constraints.
   - Unsigned mode allows only `0 ≤ key < 2^n`.
   - Invalid conversion raises `.rangeChk`.

4. [B4] Slice key extraction path.
   - For `intKey=false`, key is consumed via `popSlice`.
   - If there are fewer than `n` bits, key extraction returns `none` and execution raises `.cellUnd`.

5. [B5] Stack/type/shape checks.
   - Dict must be `.null` or `.cell`.
   - Builder must be last pushed value.
   - Wrong stack types yield `.typeChk`.
   - Stack underflow yields `.stkUnd`.

6. [B6] Dictionary update semantics for set mode.
   - `dictSetBuilderWithCells ... .set` is used.
   - Missing keys create/update dictionary and return `ok=true`.
   - On `ok=false` path with `.set`, execution throws `.fatal` (should not be reached for validated inputs).

7. [B7] Dictionary structural failures.
   - Malformed root dictionaries propagate `.dictErr`/related dictionary errors after cell-load bookkeeping.

8. [B8] Assembler encoding.
   - `.dictSetB false false .set` encodes as `0xf441`.
   - `.dictSetB true false .set` encodes as `0xf442`.
   - `.dictSetB true true .set` encodes as `0xf443`.
   - `.dictSetB false false .add`, `.dictSetB true false .add`, `.dictSetB true true .add` encode as `0xf451..0xf453`.
   - Non-set modes for `.dictSetB` (e.g. `.replace`) and `.dictSetB false true` reject with `.invOpcode`.

9. [B9] Decoder behavior.
   - `0xf441`, `0xf442`, `0xf443` decode to the three set variants.
   - Adjacent words (`0xf440`, `0xf444`) are `.invOpcode`.
   - Nearby non-set opcodes (`0xf451`) decode to different instruction families.

10. [B10] Base gas exactness branch.
   - Base gas from `computeExactGasBudget` must succeed at exact budget and fail at exact-1.

11. [B11] Gas-variable branch.
   - Set updates can create dictionary cells; cost includes `created * cellCreateGasPrice`.

TOTAL BRANCHES: 11
-/

private def suiteId : InstrId :=
  { name := "DICTSETB" }

private def instrSetSlice : Instr := .dictSetB false false .set
private def instrSetInt : Instr := .dictSetB true false .set
private def instrSetUInt : Instr := .dictSetB true true .set

private def mkBuilderValue (byte : Nat) : Builder :=
  Builder.empty.storeBits (natToBits byte 8)

private def valueA : Builder := mkBuilderValue 0xa1
private def valueB : Builder := mkBuilderValue 0xb2
private def valueC : Builder := mkBuilderValue 0xc3
private def valueD : Builder := mkBuilderValue 0xd4
private def valueE : Builder := mkBuilderValue 0xe5

private def dictNull : Value := .null

private def runDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSetB instr (VM.push (intV 909)) stack

private def runDirect (instr : Instr) : Array Value → Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSetB instr

private def mkSliceStack (root : Value) (n : Int) (key : BitString) (value : Builder) : Array Value :=
  #[.builder value, .slice (mkSliceFromBits key), root, intV n]

private def mkIntStack (root : Value) (n : Int) (key : Int) (value : Builder) : Array Value :=
  #[.builder value, intV key, root, intV n]

private def dictSetRootSlice! (label : String) (entries : Array (BitString × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetBuilderWithCells root k v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := root'
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root during construction"
      | .error e =>
          panic! s!"{label}: dict build failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: no dictionary root produced"

private def dictSetRootInt! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let kBits :=
        match dictKeyBits? k n unsigned with
        | some bits => bits
        | none => panic! s!"{label}: key out of range (k={k}, n={n}, unsigned={unsigned})"
      match dictSetBuilderWithCells root kBits v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := root'
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root during construction"
      | .error e =>
          panic! s!"{label}: dict build failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: no dictionary root produced"

private def setExpected! (root : Option Cell) (keyBits : BitString) (value : Builder) : Cell :=
  match dictSetBuilderWithCells root keyBits value .set with
  | .ok (some r, _ok, _created, _loaded) => r
  | .ok (none, _ok, _created, _loaded) => panic! "setExpected!: unexpected none root"
  | .error e => panic! s!"setExpected!: {reprStr e}"

private def setIntExpectedBits! (n : Nat) (unsigned : Bool) (root : Option Cell) (key : Int) (value : Builder) : Cell :=
  match dictKeyBits? key n unsigned with
  | some keyBits => setExpected! root keyBits value
  | none => panic! "setIntExpectedBits!: invalid key"

private def dictMalformed : Cell :=
  Cell.mkOrdinary (natToBits 0b11100 5) #[]

private def dictSlice0 : Cell := dictSetRootSlice! "dictSlice0" #[(#[], valueA)]
private def dictSlice1 : Cell := dictSetRootSlice! "dictSlice1" #[(natToBits 0 1, valueA), (natToBits 1 1, valueB)]
private def dictSlice4 : Cell := dictSetRootSlice! "dictSlice4" #[(natToBits 0 4, valueA), (natToBits 5 4, valueB), (natToBits 8 4, valueC)]
private def dictSlice8 : Cell := dictSetRootSlice! "dictSlice8" #[(natToBits 5 8, valueA), (natToBits 200 8, valueB)]
private def dictSlice16 : Cell := dictSetRootSlice! "dictSlice16" #[(natToBits 42 16, valueC), (natToBits 32767 16, valueD)]
private def dictSlice257 : Cell := dictSetRootSlice! "dictSlice257" #[(natToBits 123 257, valueA), (natToBits 321 257, valueB)]

private def dictSigned0 : Cell := dictSetRootInt! "dictSigned0" 0 false #[(0, valueA)]
private def dictSigned1 : Cell := dictSetRootInt! "dictSigned1" 1 false #[(0, valueA), (-1, valueB)]
private def dictSigned4 : Cell := dictSetRootInt! "dictSigned4" 4 false #[( -8, valueA), (-1, valueB), (0, valueC), (7, valueD)]
private def dictSigned8 : Cell := dictSetRootInt! "dictSigned8" 8 false #[( -128, valueA), (-1, valueB), (0, valueC), (42, valueD), (127, valueE)]
private def dictUnsigned8 : Cell := dictSetRootInt! "dictUnsigned8" 8 true #[(0, valueA), (1, valueB), (42, valueC), (255, valueD)]
private def dictSigned257 : Cell := dictSetRootInt! "dictSigned257" 257 false #[(0, valueA)]

private def createCountSlice (root : Option Cell) (keyBits : BitString) : Nat :=
  match dictSetBuilderWithCells root keyBits valueA .set with
  | .ok (_root, _ok, created, _loaded) => created
  | .error _ => 0

private def createCountInt (n : Nat) (unsigned : Bool) (root : Option Cell) (k : Int) : Nat :=
  match dictKeyBits? k n unsigned with
  | some keyBits =>
      match dictSetBuilderWithCells root keyBits valueA .set with
      | .ok (_root, _ok, created, _loaded) => created
      | .error _ => 0
  | none => 0

private def rawF441 : Cell := Cell.mkOrdinary (natToBits 0xf441 16) #[]
private def rawF442 : Cell := Cell.mkOrdinary (natToBits 0xf442 16) #[]
private def rawF443 : Cell := Cell.mkOrdinary (natToBits 0xf443 16) #[]
private def rawF440 : Cell := Cell.mkOrdinary (natToBits 0xf440 16) #[]
private def rawF444 : Cell := Cell.mkOrdinary (natToBits 0xf444 16) #[]
private def rawF451 : Cell := Cell.mkOrdinary (natToBits 0xf451 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrSetSlice])
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

private def expectAssemble16 (label : String) (instr : Instr) (expected : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok code =>
      if code.bits = natToBits expected 16 then
        pure ()
      else
        throw (IO.userError s!"{label}: expected bits {expected}, got {code.bits}")
  | .error e =>
      throw (IO.userError s!"{label}: assembler failed with {e}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler error {expected}")

private def expectDecode (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

private def expectDecodeInv (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr} ({bits} bits)")

private def baseGasSlice : Int := computeExactGasBudget instrSetSlice
private def baseGasInt : Int := computeExactGasBudget instrSetInt
private def gasPenalty (created : Nat) : Int := Int.ofNat created * cellCreateGasPrice

private def gasSliceInsert : Int := baseGasSlice + gasPenalty (createCountSlice none (natToBits 55 8))
private def gasSliceInsertMinusOne : Int := if gasSliceInsert > 0 then gasSliceInsert - 1 else 0
private def gasSliceHit : Int := baseGasSlice + gasPenalty (createCountSlice (some dictSlice8) (natToBits 5 8))
private def gasSliceHitMinusOne : Int := if gasSliceHit > 0 then gasSliceHit - 1 else 0
private def gasIntSignedHit : Int := baseGasInt + gasPenalty (createCountInt 8 false (some dictSigned8) 42)
private def gasIntSignedHitMinusOne : Int := if gasIntSignedHit > 0 then gasIntSignedHit - 1 else 0

private def genDictSetBFuzz (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 10 then
    -- Underflow branches [B2][B5]
    let (idx, rng2) := randNat rng1 0 3
    let c :=
      if idx = 0 then
        mkCase "fuzz/underflow/empty" #[]
      else if idx = 1 then
        mkCase "fuzz/underflow/one" #[.builder valueA]
      else if idx = 2 then
        mkCase "fuzz/underflow/two" #[.builder valueA, intV 8]
      else
        mkCase "fuzz/underflow/three" #[.builder valueA, intV 5, dictNull]
    (c, rng2)
    else if shape < 22 then
      -- n validation branches [B2]
    let (idx, rng2) := randNat rng1 0 3
    let c :=
      if idx = 0 then
        mkCase "fuzz/range/slice-nan" #[.builder valueA, .slice (mkSliceFromBits (natToBits 0 8)), dictNull, .int .nan]
      else if idx = 1 then
        mkCase "fuzz/range/slice-neg" (mkSliceStack dictNull (-1) (natToBits 0 8) valueA)
      else if idx = 2 then
        mkCase "fuzz/range/slice-too-large" (mkSliceStack dictNull 1024 (natToBits 0 8) valueA)
      else
        mkCase "fuzz/range/int-nan" #[.builder valueA, .int .nan, dictNull, intV 5]
    (c, rng2)
  else if shape < 34 then
    -- Integer-key conversion failures [B3]
    let (idx, rng2) := randNat rng1 0 3
    let c :=
      if idx = 0 then
        mkCase "fuzz/int/signed-oob-hi" (mkIntStack (.cell dictSigned8) 8 128 valueA)
      else if idx = 1 then
        mkCase "fuzz/int/signed-oob-lo" (mkIntStack (.cell dictSigned4) 4 16 valueA)
      else if idx = 2 then
        mkCase "fuzz/int/unsigned-neg" (mkIntStack (.cell dictUnsigned8) 8 (-1) valueA)
      else
        mkCase "fuzz/int/unsigned-oob" (mkIntStack (.cell dictUnsigned8) 8 256 valueA)
    (c, rng2)
  else if shape < 46 then
    -- Slice-key failures [B4]
    let (idx, rng2) := randNat rng1 0 2
    let c :=
      if idx = 0 then
        mkCase "fuzz/slice-too-short" (mkSliceStack (.cell dictSlice8) 8 (natToBits 7 4) valueA)
      else if idx = 1 then
        mkCase "fuzz/slice-too-short-257" (mkSliceStack (.cell dictSlice257) 257 (natToBits 7 128) valueA)
      else
        mkCase "fuzz/slice-hit" (mkSliceStack (.cell dictSlice8) 8 (natToBits 5 8) valueA)
    (c, rng2)
    else if shape < 58 then
      -- Type/malformed branches [B5][B7]
      let (idx, rng2) := randNat rng1 0 5
      let c :=
        if idx = 0 then
          mkCase "fuzz/type-wrong-value" #[.int (.num 7), intV 5, .cell dictSlice8, intV 8]
      else if idx = 1 then
        mkCase "fuzz/type-wrong-dict" (mkSliceStack (.int (.num 7)) 8 (natToBits 5 8) valueA)
      else if idx = 2 then
        mkCase "fuzz/type-wrong-key" #[.builder valueA, .slice (mkSliceFromBits (natToBits 5 8)), .cell dictSigned8, intV 8]
      else if idx = 3 then
        mkCase "fuzz/malformed-slice-root" (mkSliceStack (.cell dictMalformed) 8 (natToBits 5 8) valueA)
      else if idx = 4 then
        mkCase "fuzz/malformed-int-root" (mkIntStack (.cell dictMalformed) 8 5 valueA)
      else
        mkCase "fuzz/type-raw" (mkIntStack dictNull 8 1 valueA) (#[instrSetInt])
      (c, rng2)
  else if shape < 76 then
    -- Valid paths [B1][B3][B6]
    let (idx, rng2) := randNat rng1 0 5
    let c :=
      if idx = 0 then
        mkCase "fuzz/ok/slice-null-8" (mkSliceStack dictNull 8 (natToBits 55 8) valueA)
      else if idx = 1 then
        mkCase "fuzz/ok/slice-hit-4" (mkSliceStack (.cell dictSlice4) 4 (natToBits 5 4) valueC)
      else if idx = 2 then
        mkCase "fuzz/ok/int-signed-hit" (mkIntStack (.cell dictSigned8) 8 42 valueB) (program := #[instrSetInt])
      else if idx = 3 then
        mkCase "fuzz/ok/int-signed-null" (mkIntStack dictNull 8 42 valueA) (program := #[instrSetInt])
      else if idx = 4 then
        mkCase "fuzz/ok/int-unsigned-hit" (mkIntStack (.cell dictUnsigned8) 8 255 valueC) (program := #[instrSetUInt])
      else
        mkCase "fuzz/ok/int-unsigned-null" (mkIntStack dictNull 8 200 valueD) (program := #[instrSetUInt])
    (c, rng2)
  else
    -- Gas and decode probe branches [B8][B9][B10][B11]
    let (idx, rng2) := randNat rng1 0 4
    let c :=
      if idx = 0 then
        mkCodeCase "fuzz/code/441" #[] rawF441
      else if idx = 1 then
        mkCodeCase "fuzz/code/440-invalid" #[] rawF440
      else if idx = 2 then
        mkCodeCase "fuzz/code/444-invalid" #[] rawF444
      else if idx = 3 then
        mkCodeCase "fuzz/code/451-not-dictsetb" #[] rawF451
      else
        mkCase "fuzz/gas-minus-one-truncated" #[] (#[.pushInt (.num gasSliceInsertMinusOne), .tonEnvOp .setGasLimit, instrSetSlice])
          (oracleGasLimitsExactMinusOne gasSliceInsertMinusOne)
    (c, rng2)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDispatchFallback .add #[] with
        | .ok st =>
            if st == #[intV 909] then
              pure ()
            else
              throw (IO.userError s!"fallback mismatch: got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"fallback failed: {e}") },
    { name := "unit/asm/valid" -- [B8]
      run := do
        expectAssemble16 "asm/f441" instrSetSlice 0xf441
        expectAssemble16 "asm/f442" instrSetInt 0xf442
        expectAssemble16 "asm/f443" instrSetUInt 0xf443
        expectAssemble16 "asm/f451" (.dictSetB false false .add) 0xf451
        expectAssemble16 "asm/f452" (.dictSetB true false .add) 0xf452
        expectAssemble16 "asm/f453" (.dictSetB true true .add) 0xf453 },
    { name := "unit/asm/reject" -- [B8]
      run := do
        expectAssembleErr "asm/reject-unsigned-slice" (.dictSetB false true .set) .invOpcode
        expectAssembleErr "asm/reject-set-replace" (.dictSetB false false .replace) .invOpcode
        pure () },
    { name := "unit/decode/valid" -- [B9]
      run := do
        expectDecode "decode/f441" rawF441 instrSetSlice
        expectDecode "decode/f442" rawF442 instrSetInt
        expectDecode "decode/f443" rawF443 instrSetUInt },
    { name := "unit/decode/invalid-and-aliased" -- [B9]
      run := do
        expectDecodeInv "decode/f440" rawF440
        expectDecodeInv "decode/f444" rawF444
        match decodeCp0WithBits (Slice.ofCell rawF451) with
        | .ok (instr, bits, _) =>
            if instr == instrSetSlice then
              throw (IO.userError "decode/f451 unexpectedly decoded to DICTSETB")
            else if bits != 16 then
              throw (IO.userError "decode/f451 did not consume 16 bits")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"decode/f451 expected non-DICTSETB instruction, got {e}") },
    { name := "unit/exec/success/slice-null" -- [B6]
      run := do
        let expected := setExpected! none (natToBits 5 8) valueA
        expectOkStack "slice-null" (runDirect instrSetSlice (mkSliceStack dictNull 8 (natToBits 5 8) valueA)) #[.cell expected] },
    { name := "unit/exec/success/slice-hit" -- [B6]
      run := do
        let expected := setExpected! (some dictSlice8) (natToBits 5 8) valueC
        expectOkStack "slice-hit" (runDirect instrSetSlice (mkSliceStack (.cell dictSlice8) 8 (natToBits 5 8) valueC)) #[.cell expected] },
    { name := "unit/exec/success/int-signed-hit" -- [B3][B6]
      run := do
        let expected := setIntExpectedBits! 8 false (some dictSigned8) 42 valueD
        expectOkStack "int-signed-hit" (runDirect instrSetInt (mkIntStack (.cell dictSigned8) 8 42 valueD)) #[.cell expected] },
    { name := "unit/exec/success/int-unsigned-hit" -- [B3][B6]
      run := do
        let expected := setIntExpectedBits! 8 true (some dictUnsigned8) 255 valueE
        expectOkStack "int-unsigned-hit" (runDirect instrSetUInt (mkIntStack (.cell dictUnsigned8) 8 255 valueE)) #[.cell expected] },
    { name := "unit/exec/error/underflow" -- [B2][B5]
      run := do
        expectErr "underflow-empty" (runDirect instrSetSlice #[]) .stkUnd
        expectErr "underflow-one" (runDirect instrSetSlice #[.builder valueA]) .stkUnd
        expectErr "underflow-two" (runDirect instrSetSlice #[.builder valueA, intV 8]) .stkUnd },
    { name := "unit/exec/error/n-range" -- [B2]
      run := do
        expectErr "range-nan" (runDirect instrSetSlice #[.builder valueA, .slice (mkSliceFromBits (natToBits 5 8)), dictNull, .int .nan]) .rangeChk
        expectErr "range-neg" (runDirect instrSetSlice (mkSliceStack dictNull (-1) (natToBits 5 8) valueA)) .rangeChk
        expectErr "range-too-large" (runDirect instrSetSlice (mkSliceStack dictNull 1024 (natToBits 5 8) valueA)) .rangeChk },
    { name := "unit/exec/error/int-key-range" -- [B3]
      run := do
        expectErr "key-signed-oob-hi" (runDirect instrSetInt (mkIntStack dictNull 8 128 valueA)) .rangeChk
        expectErr "key-signed-oob-lo" (runDirect instrSetInt (mkIntStack dictNull 1 2 valueA)) .rangeChk
        expectErr "key-unsigned-neg" (runDirect instrSetUInt (mkIntStack dictNull 8 (-1) valueA)) .rangeChk },
    { name := "unit/exec/error/slice-underflow" -- [B4]
      run := do
        expectErr "slice-underflow" (runDirect instrSetSlice (mkSliceStack dictNull 8 (natToBits 7 4) valueA)) .cellUnd },
    { name := "unit/exec/error/type-and-structure" -- [B5][B7]
      run := do
        expectErr "type-dict" (runDirect instrSetSlice (mkSliceStack (.int (.num 7)) 8 (natToBits 5 8) valueA)) .typeChk
        expectErr "type-key" (runDirect instrSetInt #[.builder valueA, .slice (mkSliceFromBits (natToBits 5 8)), .cell dictSigned8, intV 8]) .typeChk
        expectErr "type-value" (runDirect instrSetSlice (#[.int (.num 7), .slice (mkSliceFromBits (natToBits 5 8)), .cell dictSlice8, intV 8])) .typeChk
        expectErr "bad-root" (runDirect instrSetSlice (mkSliceStack (.cell dictMalformed) 8 (natToBits 5 8) valueA)) .cellUnd },
    { name := "unit/gas/exact-and-minus-one" -- [B10][B11]
      run := do
        expectOkStack "gas-exact-insert" (runDirect instrSetSlice (mkSliceStack dictNull 8 (natToBits 55 8) valueA))
          #[.cell (setExpected! none (natToBits 55 8) valueA)]
      }
  ]
  oracle := #[
    mkCase "ok/slice/null/0" (mkSliceStack dictNull 0 #[] valueA), -- [B2][B4][B6]
    mkCase "ok/slice/null/1" (mkSliceStack dictNull 1 (natToBits 1 1) valueB), -- [B2][B4][B6]
    mkCase "ok/slice/null/4" (mkSliceStack dictNull 4 (natToBits 7 4) valueC), -- [B2][B4][B6]
    mkCase "ok/slice/null/8" (mkSliceStack dictNull 8 (natToBits 55 8) valueA), -- [B2][B4][B6]
    mkCase "ok/slice/hit/4" (mkSliceStack (.cell dictSlice4) 4 (natToBits 5 4) valueD), -- [B4][B6]
    mkCase "ok/slice/hit/8" (mkSliceStack (.cell dictSlice8) 8 (natToBits 5 8) valueB), -- [B4][B6]
    mkCase "ok/slice/split/8" (mkSliceStack (.cell dictSlice8) 8 (natToBits 200 8) valueC), -- [B4][B6]
    mkCase "ok/slice/hit/16" (mkSliceStack (.cell dictSlice16) 16 (natToBits 42 16) valueD), -- [B4][B6]
    mkCase "ok/slice/hit/257" (mkSliceStack (.cell dictSlice257) 257 (natToBits 123 257) valueE), -- [B4][B6]

    mkCase "ok/int/signed/null/0" (mkIntStack dictNull 0 0 valueA) (program := #[instrSetInt]), -- [B2][B3][B6]
    mkCase "ok/int/signed/null/1" (mkIntStack dictNull 1 0 valueB) (program := #[instrSetInt]), -- [B2][B3][B6]
    mkCase "ok/int/signed/hit/1" (mkIntStack (.cell dictSigned1) 1 (-1) valueC) (program := #[instrSetInt]), -- [B2][B3][B6]
    mkCase "ok/int/signed/hit/4" (mkIntStack (.cell dictSigned4) 4 7 valueD) (program := #[instrSetInt]), -- [B2][B3][B6]
    mkCase "ok/int/signed/hit/8" (mkIntStack (.cell dictSigned8) 8 42 valueE) (program := #[instrSetInt]), -- [B2][B3][B6]
    mkCase "ok/int/unsigned/null/8" (mkIntStack dictNull 8 200 valueA) (program := #[instrSetUInt]), -- [B2][B3][B6]
    mkCase "ok/int/unsigned/hit/8" (mkIntStack (.cell dictUnsigned8) 8 255 valueD) (program := #[instrSetUInt]), -- [B2][B3][B6]

    mkCodeCase "decode/f441" #[] rawF441, -- [B9]
    mkCodeCase "decode/f442" #[] rawF442, -- [B9]
    mkCodeCase "decode/f443" #[] rawF443, -- [B9]
    mkCodeCase "decode/f440-invalid" #[] rawF440, -- [B9]
    mkCodeCase "decode/f444-invalid" #[] rawF444, -- [B9]
    mkCodeCase "decode/f451-not-dictset" #[] rawF451, -- [B9]
    mkCodeCase "decode/truncated8" #[] rawTruncated8, -- [B9]

    mkCase "err/underflow/empty" #[], -- [B2][B5]
    mkCase "err/underflow/one" #[.builder valueA], -- [B2][B5]
    mkCase "err/underflow/two" #[.builder valueA, intV 8], -- [B2][B5]
    mkCase "err/underflow/three" (mkSliceStack dictNull 8 (natToBits 5 8) valueA), -- [B2][B5]
    mkCase "err/nan" (#[.builder valueA, .slice (mkSliceFromBits (natToBits 7 8)), dictNull, .int .nan]), -- [B2]
    mkCase "err/n-neg" (mkSliceStack dictNull (-1) (natToBits 7 8) valueA), -- [B2]
    mkCase "err/n-too-large" (mkSliceStack dictNull 1024 (natToBits 7 8) valueA), -- [B2]
    mkCase "err/int-key-range-hi" (mkIntStack dictNull 8 256 valueA) (program := #[instrSetUInt]), -- [B3]
    mkCase "err/int-key-range-lo" (mkIntStack dictNull 4 8 valueA) (program := #[instrSetInt]), -- [B3]
    mkCase "err/int-key-neg-unsigned" (mkIntStack dictNull 8 (-1) valueA) (program := #[instrSetUInt]), -- [B3]
    mkCase "err/slice-key-too-short" (mkSliceStack (.cell dictSlice8) 8 (natToBits 5 4) valueA), -- [B4]
    mkCase "err/type-dict" (mkSliceStack (.int (.num 7)) 8 (natToBits 5 8) valueA), -- [B5]
    mkCase "err/type-key-int" #[.builder valueA, .slice (mkSliceFromBits (natToBits 5 8)), .cell dictSigned8, intV 8], -- [B5]
    mkCase "err/type-value" (#[.int (.num 7), intV 5, .cell dictSlice8, intV 8]), -- [B5]
    mkCase "err/dict-err-slice-root" (mkSliceStack (.cell dictMalformed) 8 (natToBits 5 8) valueA), -- [B7]
    mkCase "err/dict-err-int-root" (mkIntStack (.cell dictMalformed) 8 5 valueA) (program := #[instrSetInt]), -- [B7]

    mkCase "gas/slice-insert" (mkSliceStack dictNull 8 (natToBits 55 8) valueA)
      (program := #[instrSetSlice]) (gasLimits := oracleGasLimitsExact gasSliceInsert), -- [B10][B11]
    mkCase "gas/slice-minus-one" (mkSliceStack dictNull 8 (natToBits 55 8) valueA)
      (program := #[instrSetSlice]) (gasLimits := oracleGasLimitsExactMinusOne gasSliceInsertMinusOne), -- [B10][B11]
    mkCase "gas/slice-hit" (mkSliceStack (.cell dictSlice8) 8 (natToBits 5 8) valueA)
      (program := #[instrSetSlice]) (gasLimits := oracleGasLimitsExact gasSliceHit), -- [B10][B11]
    mkCase "gas/int-hit" (mkIntStack (.cell dictSigned8) 8 42 valueA)
      (program := #[instrSetInt]) (gasLimits := oracleGasLimitsExact gasIntSignedHit), -- [B10][B11]
    mkCase "gas/int-minus-one" (mkIntStack (.cell dictSigned8) 8 42 valueA)
      (program := #[instrSetInt]) (gasLimits := oracleGasLimitsExactMinusOne gasIntSignedHitMinusOne) -- [B10][B11]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictSetBFuzz }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTSETB
