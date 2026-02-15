import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTISETGET

/-!
INSTRUCTION: DICTISETGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictExt` handles `.dictExt (.mutGet ... .set)` and only forwards matching
     `dictExt` variants into this branch.
   - Non-matching instruction/opcode must follow `next`.

2. [B2] Runtime arity and width validation.
   - `checkUnderflow 4` guards `newValue`, `key`, `dict`, `n`.
   - `popNatUpTo 1023` validates `n`, with negative/NaN/`>1023` producing `.rangeChk`.

3. [B3] Integer-key conversion and `n=0` edge behavior.
   - Signed mode uses `dictKeyBits?` with `unsigned = false`.
   - Unsigned mode uses `dictKeyBits?` with `unsigned = true`.
    - Out-of-range keys (e.g. n=4 and key=8 / -9 or unsigned -1/16) raise `.rangeChk`.
   - `n = 0` only permits key `0`; all other keys raise `.rangeChk`.

4. [B4] Type checking and argument ordering.
   - `newValue`: must be a slice for non-ref mode and a cell for ref mode.
   - `dict`: must be `null` or `.cell`.
   - `key`: must be `int` in signed/unsigned set/get variants.

5. [B5] Runtime set semantics.
   - Existing key (hit): returns updated root, old value, and `-1`.
   - Missing key (miss): returns new root and `0`, including on `.null` root.
   - Unsigned and by-ref variants are handled through the same mutGet family.

6. [B6] Dictionary structural/malformed payload errors.
   - Ref extraction for `.mutGet ... byRef` requires old payload slice with exactly
     `bitsRemaining = 0` and `refsRemaining = 1`.
   - Violations are reported as `.dictErr`.
   - Corrupt dictionary roots are also propagated as `.dictErr`.

7. [B7] Assembler behavior.
   - `assembleCp0` encodes `.dictExt (.mutGet ... .set)` forms (16-bit opcodes `0xF41A..0xF41F`).

8. [B8] Decoder behavior and opcode aliasing.
   - `0xF41A..0xF41F` map to `.dictExt (.mutGet ... .set)` with opcode bits:
     intKey/unsigned/byRef in low bits.
   - `0xF419`, `0xF420`, and truncated `0xF4` must decode as `.invOpcode`.

9. [B9] Gas accounting.
   - Base execution gas from `computeExactGasBudget`.
   - Hit/miss branches include variable `created` charges (`cellCreateGasPrice * created`).
   - Exact and exact-minus-one limits must be checked on both happy paths and insertion paths.

10. [B10] Fuzzer coverage.
   - Any branch not explicitly listed as oracle must be hit by explicit fuzz shapes (including errors, decoder variants, and gas).

11. [B11] Runtime by-reference family behavior.
   - `.dictExt (.mutGet true false true .set)` and `.dictExt (.mutGet true true true .set)` are covered to exercise
     by-ref payload shape checks and unsigned integer key conversion.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests must be covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTISETGET" }

private def instrSigned : Instr :=
  .dictExt (.mutGet true false false .set)

private def instrUnsigned : Instr :=
  .dictExt (.mutGet true true false .set)

private def instrSignedRef : Instr :=
  .dictExt (.mutGet true false true .set)

private def instrUnsignedRef : Instr :=
  .dictExt (.mutGet true true true .set)

private def instrSlice : Instr :=
  .dictExt (.mutGet false false false .set)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawCode (intKey unsigned byRef : Bool) : Nat :=
  0xF41A ||| (if intKey then 4 else 0) ||| (if unsigned then 2 else 0) ||| (if byRef then 1 else 0)

private def rawF41A : Cell := raw16 (rawCode false false false)
private def rawF41B : Cell := raw16 (rawCode false false true)
private def rawF41C : Cell := raw16 (rawCode true false false)
private def rawF41D : Cell := raw16 (rawCode true false true)
private def rawF41E : Cell := raw16 (rawCode true true false)
private def rawF41F : Cell := raw16 (rawCode true true true)
private def rawF41Gap : Cell := raw16 0xF419
private def rawF420 : Cell := raw16 0xF420
private def rawTrunc8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def valueA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xE5 8)

private def valueCellA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueCellB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueCellC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def valueCellD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]
private def valueCellE : Cell := Cell.mkOrdinary (natToBits 0xE5 8) #[]
private def valueCellF : Cell := Cell.mkOrdinary (natToBits 0xF6 8) #[]

private def valueCellRefA : Cell := Cell.mkOrdinary #[] #[valueCellA]
private def valueCellRefB : Cell := Cell.mkOrdinary #[] #[valueCellB]

private def valueSliceBadBits : Slice := mkSliceFromBits (natToBits 1 1)
private def valueSliceTwoRefs : Slice :=
  Slice.ofCell (Cell.mkOrdinary #[] #[valueCellA, valueCellB])
private def valueSliceNoRef : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[])
private def valueSliceValidRef : Slice :=
  Slice.ofCell (Cell.mkOrdinary #[] #[valueCellA])

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def keyBitsFor (label : String) (n : Nat) (unsigned : Bool) (k : Int) : BitString :=
  match dictKeyBits? k n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid integer key {k} for n={n}, unsigned={unsigned}"

private def mkDictSetSliceBitsRoot! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetSliceWithCells root k v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dict set returned no root"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary root"

private def mkDictSetSliceIntRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) (unsigned : Bool := false) : Cell :=
  mkDictSetSliceBitsRoot! label (entries.map fun p => (keyBitsFor label n unsigned p.1, p.2))

private def mkDictSetRefBitsRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetRefWithCells root k v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dict set returned no root"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary root"

private def mkDictSetRefIntRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) (unsigned : Bool := false) : Cell :=
  mkDictSetRefBitsRoot! label (entries.map fun p => (keyBitsFor label n unsigned p.1, p.2))

private def dictSigned4 : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGET.dictSigned4" 4 #[
    ((-8 : Int), valueA),
    ((-1 : Int), valueB),
    ((0 : Int), valueC),
    ((7 : Int), valueD)
  ]

private def dictSigned0 : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGET.dictSigned0" 0 #[(0, valueE)]

private def dictUnsigned4 : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGET.dictUnsigned4" 4 #[
    ((0 : Int), valueA),
    ((1 : Int), valueB),
    ((9 : Int), valueC),
    ((15 : Int), valueD)
  ] (unsigned := true)

private def dictSigned4RefOk : Cell :=
  mkDictSetRefIntRoot! "DICTISETGET.dictSigned4RefOk" 4 #[
    ((5 : Int), valueCellRefA),
    ((6 : Int), valueCellRefB)
  ]

private def dictSigned4RefBadBits : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGET.dictSigned4RefBadBits" 4 #[
    ((5 : Int), valueSliceBadBits),
    ((6 : Int), valueC)
  ]

private def dictSigned4RefBadRefs : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGET.dictSigned4RefBadRefs" 4 #[
    ((5 : Int), valueSliceTwoRefs),
    ((6 : Int), valueC)
  ]

private def dictSigned4RefBadNoRef : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGET.dictSigned4RefBadNoRef" 4 #[
    ((5 : Int), valueSliceNoRef),
    ((6 : Int), valueC)
  ]

private def expectSetRootSlice
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (unsigned : Bool)
    (key : Int)
    (value : Slice) : Cell :=
  match dictLookupSetSliceWithCells root (keyBitsFor label n unsigned key) value .set with
  | .ok (_, some r, _ok, _created, _loaded) => r
  | .ok (_, none, _ok, _created, _loaded) =>
      panic! s!"{label}: expected new root, got none"
  | .error e =>
      panic! s!"{label}: dictLookupSetSliceWithCells failed ({reprStr e})"

private def expectSetRootRef
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (unsigned : Bool)
    (key : Int)
    (value : Cell) : Cell :=
  match dictLookupSetRefWithCells root (keyBitsFor label n unsigned key) value .set with
  | .ok (_, some r, _ok, _created, _loaded) => r
  | .ok (_, none, _ok, _created, _loaded) =>
      panic! s!"{label}: expected new root, got none"
  | .error e =>
      panic! s!"{label}: dictLookupSetRefWithCells failed ({reprStr e})"

private def expectSetCreatedSlice
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (unsigned : Bool)
    (key : Int)
    (value : Slice) : Nat :=
  match dictLookupSetSliceWithCells root (keyBitsFor label n unsigned key) value .set with
  | .ok (_, _, _ok, created, _loaded) => created
  | .error e =>
      panic! s!"{label}: dictLookupSetSliceWithCells failed ({reprStr e})"

private def expectedReplaceSignedNeg8 : Cell :=
  expectSetRootSlice "expectedReplaceSignedNeg8" (some dictSigned4) 4 false (-8) valueE

private def expectedReplaceSignedMinus1 : Cell :=
  expectSetRootSlice "expectedReplaceSignedMinus1" (some dictSigned4) 4 false (-1) valueB

private def expectedInsertSigned1Null : Cell :=
  expectSetRootSlice "expectedInsertSigned1Null" none 4 false 1 valueA

private def expectedInsertSigned1 : Cell :=
  expectSetRootSlice "expectedInsertSigned1" (some dictSigned4) 4 false 1 valueB

private def expectedSignedZeroWidth : Cell :=
  expectSetRootSlice "expectedSignedZeroWidth" (some dictSigned0) 0 false 0 valueD

private def expectedReplaceUnsigned15 : Cell :=
  expectSetRootSlice "expectedReplaceUnsigned15" (some dictUnsigned4) 4 true 15 valueE

private def expectedInsertUnsigned3Null : Cell :=
  expectSetRootSlice "expectedInsertUnsigned3Null" none 4 true 3 valueC

private def expectedInsertUnsigned3 : Cell :=
  expectSetRootSlice "expectedInsertUnsigned3" (some dictUnsigned4) 4 true 3 valueA

private def expectedReplaceRef5 : Cell :=
  expectSetRootRef "expectedReplaceRef5" (some dictSigned4RefOk) 4 false 5 valueCellD

private def expectedInsertRefNull : Cell :=
  expectSetRootRef "expectedInsertRefNull" none 4 false 5 valueCellA

private def baseGas : Int :=
  computeExactGasBudget instrSigned

private def signedHitCreated : Nat :=
  expectSetCreatedSlice "signedHitCreated" (some dictSigned4) 4 false (-8) valueE

private def signedMissNullCreated : Nat :=
  expectSetCreatedSlice "signedMissNullCreated" none 4 false 1 valueA

private def signedMissNonEmptyCreated : Nat :=
  expectSetCreatedSlice "signedMissNonEmptyCreated" (some dictSigned4) 4 false 1 valueB

private def signedHitGas : Int :=
  baseGas + (Int.ofNat signedHitCreated * cellCreateGasPrice)

private def signedMissNullGas : Int :=
  baseGas + (Int.ofNat signedMissNullCreated * cellCreateGasPrice)

private def signedMissNonEmptyGas : Int :=
  baseGas + (Int.ofNat signedMissNonEmptyCreated * cellCreateGasPrice)

private def unsignedHitGas : Int :=
  baseGas + (Int.ofNat (expectSetCreatedSlice "unsignedHitCreated" (some dictUnsigned4) 4 true 15 valueA) * cellCreateGasPrice)

private def unsignedMissNullGas : Int :=
  baseGas + (Int.ofNat (expectSetCreatedSlice "unsignedMissNullCreated" none 4 true 3 valueC) * cellCreateGasPrice)

private def baseGasMinusOne : Int :=
  if baseGas > 0 then baseGas - 1 else 0

private def signedHitGasMinusOne : Int :=
  if signedHitGas > 0 then signedHitGas - 1 else 0

private def signedMissNullGasMinusOne : Int :=
  if signedMissNullGas > 0 then signedMissNullGas - 1 else 0

private def signedMissNonEmptyGasMinusOne : Int :=
  if signedMissNonEmptyGas > 0 then signedMissNonEmptyGas - 1 else 0

private def unsignedHitGasMinusOne : Int :=
  if unsignedHitGas > 0 then unsignedHitGas - 1 else 0

private def unsignedMissNullGasMinusOne : Int :=
  if unsignedMissNullGas > 0 then unsignedMissNullGas - 1 else 0

private def gasLimitsExactSignedHit : OracleGasLimits := oracleGasLimitsExact signedHitGas
private def gasLimitsExactSignedMissNull : OracleGasLimits := oracleGasLimitsExact signedMissNullGas
private def gasLimitsExactSignedMissNonEmpty : OracleGasLimits := oracleGasLimitsExact signedMissNonEmptyGas
private def gasLimitsExactUnsignedHit : OracleGasLimits := oracleGasLimitsExact unsignedHitGas
private def gasLimitsExactUnsignedMiss : OracleGasLimits := oracleGasLimitsExact unsignedMissNullGas
private def gasLimitsBaseExact : OracleGasLimits := oracleGasLimitsExact baseGas
private def gasLimitsBaseExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne
private def gasLimitsSignedHitMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne signedHitGasMinusOne
private def gasLimitsSignedMissNullMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne signedMissNullGasMinusOne
private def gasLimitsSignedMissNonEmptyMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne signedMissNonEmptyGasMinusOne
private def gasLimitsUnsignedHitMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne unsignedHitGasMinusOne
private def gasLimitsUnsignedMissMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne unsignedMissNullGasMinusOne

private def mkGasProgram (raw : Cell) (gasLimit : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gasLimit), .tonEnvOp .setGasLimit ] with
  | .ok c =>
      Cell.mkOrdinary (c.bits ++ raw.bits) #[]
  | .error e =>
      panic! s!"DICTISETGET: could not assemble gas program ({reprStr e})"

private def mkSignedStack (value : Slice) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[.slice value, .int (.num key), dict, intV n]

private def mkRefStack (value : Cell) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[.cell value, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some rawF41C
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
    (raw : Cell)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some (mkGasProgram raw gas)
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeStep
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (i, bits, rest) =>
      if i != expected || bits != 16 || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected {expected}, got {i}, {bits}, {rest.bitsRemaining}/{rest.refsRemaining}")

private def expectDecodeInvOpcode
    (label : String)
    (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} ({bits})")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleInvOpcode
    (label : String)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected .invOpcode")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def expectAssembleOk16
    (label : String)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assembly success, got {e}")
  | .ok code =>
      expectDecodeStep label code instr

private def expectHitSliceShape
    (label : String)
    (result : Except Excno (Array Value))
    (expectedRoot : Cell) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")
  | .ok st =>
      match st with
      | #[root, .slice _, flag] =>
          if root != Value.cell expectedRoot then
            throw (IO.userError s!"{label}: expected root {reprStr (Value.cell expectedRoot)}, got {reprStr root}")
          else if flag != intV (-1) then
            throw (IO.userError s!"{label}: expected -1 flag, got {reprStr flag}")
          else
            pure ()
      | _ =>
          throw (IO.userError s!"{label}: expected [cell, slice, -1], got {reprStr st}")

private def expectHitRefShape
    (label : String)
    (result : Except Excno (Array Value))
    (expectedRoot : Cell) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")
  | .ok st =>
      match st with
      | #[root, .cell _, flag] =>
          if root != Value.cell expectedRoot then
            throw (IO.userError s!"{label}: expected root {reprStr (Value.cell expectedRoot)}, got {reprStr root}")
          else if flag != intV (-1) then
            throw (IO.userError s!"{label}: expected -1 flag, got {reprStr flag}")
          else
            pure ()
      | _ =>
          throw (IO.userError s!"{label}: expected [cell, cell, -1], got {reprStr st}")

private def runDICTISETGETFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV 777)) stack

private def runDICTISETGETSigned (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrSigned stack

private def runDICTISETGETUnsigned (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrUnsigned stack

private def runDICTISETGETRef (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrSignedRef stack

private def runDICTISETGETUnsignedRef (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrUnsignedRef stack

private def genDICTISETGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 40
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[], rng2)
    else if shape = 1 then
      (mkCase "fuzz/underflow/one" #[.slice valueA], rng2)
    else if shape = 2 then
      (mkCase "fuzz/underflow/two" #[.slice valueA, .int (.num 1)], rng2)
    else if shape = 3 then
      (mkCase "fuzz/underflow/three" #[.slice valueA, .int (.num 1), .cell dictSigned4], rng2)
    else if shape = 4 then
      (mkCase "fuzz/signed/hit/-8" (mkSignedStack valueC (-8) (.cell dictSigned4) 4), rng2)
    else if shape = 5 then
      (mkCase "fuzz/signed/miss/null" (mkSignedStack valueD 1 (.null) 4), rng2)
    else if shape = 6 then
      (mkCase "fuzz/signed/miss/nonempty" (mkSignedStack valueB 1 (.cell dictSigned4) 4), rng2)
    else if shape = 7 then
      (mkCase "fuzz/signed/miss/zero" (mkSignedStack valueA 0 (.cell dictSigned0) 0), rng2)
    else if shape = 8 then
      (mkCodeCase "fuzz/unsigned/hit/15" (mkSignedStack valueA 15 (.cell dictUnsigned4) 4) rawF41E, rng2)
    else if shape = 9 then
      (mkCodeCase "fuzz/unsigned/miss/null" (mkSignedStack valueC 3 (.null) 4) rawF41E, rng2)
    else if shape = 10 then
      (mkCodeCase "fuzz/unsigned/miss/nonempty" (mkSignedStack valueE 3 (.cell dictUnsigned4) 4) rawF41E, rng2)
    else if shape = 11 then
      (mkCodeCase "fuzz/ref/hit/5" (mkRefStack valueCellD 5 (.cell dictSigned4RefOk) 4) rawF41D, rng2)
    else if shape = 12 then
      (mkCodeCase "fuzz/ref/miss/null" (mkRefStack valueCellA 3 (.null) 4) rawF41D, rng2)
    else if shape = 13 then
      (mkCodeCase "fuzz/ref/miss/nonempty" (mkRefStack valueCellB 1 (.cell dictSigned4RefOk) 4) rawF41D, rng2)
    else if shape = 14 then
      (mkCodeCase "fuzz/ref/malformed/bad-bits" (mkRefStack valueCellB 5 (.cell dictSigned4RefBadBits) 4) rawF41D, rng2)
    else if shape = 15 then
      (mkCodeCase "fuzz/ref/malformed/two-refs" (mkRefStack valueCellB 5 (.cell dictSigned4RefBadRefs) 4) rawF41D, rng2)
    else if shape = 16 then
      (mkCodeCase "fuzz/ref/malformed/no-ref" (mkRefStack valueCellB 5 (.cell dictSigned4RefBadNoRef) 4) rawF41D, rng2)
    else if shape = 17 then
      (mkCase "fuzz/signed/key-high/8" (mkSignedStack valueA 8 (.cell dictSigned4) 4), rng2)
    else if shape = 18 then
      (mkCase "fuzz/signed/key-low/-9" (mkSignedStack valueA (-9) (.cell dictSigned4) 4), rng2)
    else if shape = 19 then
      (mkCodeCase "fuzz/unsigned/key-negative" (mkSignedStack valueA (-1) (.cell dictUnsigned4) 4) rawF41E, rng2)
    else if shape = 20 then
      (mkCodeCase "fuzz/unsigned/key-high/16" (mkSignedStack valueA 16 (.cell dictUnsigned4) 4) rawF41E, rng2)
    else if shape = 21 then
      (mkCase "fuzz/n-negative" (mkSignedStack valueA 1 (.cell dictSigned4) (-1)), rng2)
    else if shape = 22 then
      (mkCase "fuzz/n-too-large" (mkSignedStack valueA 1 (.cell dictSigned4) 1024), rng2)
    else if shape = 23 then
      (mkCase "fuzz/n-nan" (#[.slice valueA, .int (.num 1), .cell dictSigned4, .int .nan]), rng2)
    else if shape = 24 then
      (mkCase "fuzz/type/value-not-slice" #[.int (.num 1), .int (.num 1), .cell dictSigned4, intV 4], rng2)
    else if shape = 25 then
      (mkCase "fuzz/type/key-not-int" (#[.slice valueA, .slice valueB, .cell dictSigned4, intV 4]), rng2)
    else if shape = 26 then
      (mkCase "fuzz/type/dict-not-root" (mkSignedStack valueA (-8) (.tuple #[]) 4), rng2)
    else if shape = 27 then
      (mkCase "fuzz/malformed-root/signed" (mkSignedStack valueA 5 (.cell malformedDict) 4), rng2)
    else if shape = 28 then
      (mkCodeCase "fuzz/malformed-root/unsigned" (mkSignedStack valueA 5 (.cell malformedDict) 4) rawF41E, rng2)
    else if shape = 29 then
      (mkCodeCase "fuzz/malformed-root/ref" (mkRefStack valueCellA 5 (.cell malformedDict) 4) rawF41D, rng2)
    else if shape = 30 then
      (mkGasCase "fuzz/gas/exact/signed-hit" (mkSignedStack valueC (-8) (.cell dictSigned4) 4) rawF41C signedHitGas gasLimitsExactSignedHit, rng2)
    else if shape = 31 then
      (mkGasCase "fuzz/gas/exact/signed-miss-null" (mkSignedStack valueD 1 (.null) 4) rawF41C signedMissNullGas gasLimitsExactSignedMissNull, rng2)
    else if shape = 32 then
      (mkGasCase "fuzz/gas/exact/unsigned-hit" (mkSignedStack valueA 15 (.cell dictUnsigned4) 4) rawF41E unsignedHitGas gasLimitsExactUnsignedHit, rng2)
    else if shape = 33 then
      (mkGasCase "fuzz/gas/exact/unsigned-miss" (mkSignedStack valueC 3 (.null) 4) rawF41E unsignedMissNullGas gasLimitsExactUnsignedMiss, rng2)
    else if shape = 34 then
      (mkGasCase "fuzz/gas/exact-minus-one/signed-miss-nonempty" (mkSignedStack valueB 1 (.cell dictSigned4) 4) rawF41C signedMissNonEmptyGasMinusOne gasLimitsSignedMissNonEmptyMinusOne, rng2)
    else if shape = 35 then
      (mkCodeCase "fuzz/decode/f41a" (mkSignedStack valueA 0 (.cell dictSigned4) 4) rawF41A, rng2)
    else if shape = 36 then
      (mkCodeCase "fuzz/decode/f41b" (mkSignedStack valueA 0 (.cell dictSigned4) 4) rawF41B, rng2)
    else if shape = 37 then
      (mkCodeCase "fuzz/decode/f41c" (mkSignedStack valueA 0 (.cell dictSigned4) 4) rawF41C, rng2)
    else if shape = 38 then
      (mkCodeCase "fuzz/decode/f41d" (mkRefStack valueCellA 0 (.null) 4) rawF41D, rng2)
    else if shape = 39 then
      (mkCodeCase "fuzz/decode/f41e" (mkSignedStack valueA 0 (.null) 4) rawF41E, rng2)
    else if shape = 40 then
      (mkCodeCase "fuzz/decode/f41f" (mkRefStack valueCellA 0 (.null) 4) rawF41F, rng2)
    else
      (mkCodeCase s!"fuzz/noise/{tag}" (mkSignedStack valueA 7 (.cell dictSigned4) 4) rawF420, rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    -- [B1] runtime dispatch.
    { name := "unit/dispatch/fallback"
      run := do
        let out := runDICTISETGETFallback #[]
        expectOkStack "unit/dispatch/fallback" out #[intV 777] },
    -- [B8] decoder mapping for valid opcode f41a.
    { name := "unit/decode/f41a"
      run := do
        expectDecodeStep "unit/decode/f41a" rawF41A (.dictExt (.mutGet false false false .set)) },
    -- [B8] decoder mapping for valid opcode f41b.
    { name := "unit/decode/f41b"
      run := do
        expectDecodeStep "unit/decode/f41b" rawF41B (.dictExt (.mutGet false false true .set)) },
    -- [B8] decoder mapping for valid opcode f41c.
    { name := "unit/decode/f41c"
      run := do
        expectDecodeStep "unit/decode/f41c" rawF41C (.dictExt (.mutGet true true false .set)) },
    -- [B8] decoder mapping for valid opcode f41d.
    { name := "unit/decode/f41d"
      run := do
        expectDecodeStep "unit/decode/f41d" rawF41D (.dictExt (.mutGet true true true .set)) },
    -- [B8] decoder mapping for valid opcode f41e.
    { name := "unit/decode/f41e"
      run := do
        expectDecodeStep "unit/decode/f41e" rawF41E (.dictExt (.mutGet true true false .set)) },
    -- [B8] decoder mapping for valid opcode f41f.
    { name := "unit/decode/f41f"
      run := do
        expectDecodeStep "unit/decode/f41f" rawF41F (.dictExt (.mutGet true true true .set)) },
    -- [B8] decoder boundaries and truncation reject with invOpcode.
    { name := "unit/decode/gap"
      run := do
        expectDecodeInvOpcode "unit/decode/f419" rawF41Gap
        expectDecodeInvOpcode "unit/decode/f420" rawF420
        expectDecodeInvOpcode "unit/decode/trunc-8" rawTrunc8 },
    -- [B7] assembler encodes dictExt mutGet set forms.
    { name := "unit/assemble/encodes"
      run := do
        expectAssembleOk16 "unit/assemble/encodes/slice" instrSlice
        expectAssembleOk16 "unit/assemble/encodes/signed" instrSigned
        expectAssembleOk16 "unit/assemble/encodes/unsigned" instrUnsigned
        expectAssembleOk16 "unit/assemble/encodes/ref" instrSignedRef
        expectAssembleOk16 "unit/assemble/encodes/unsigned-ref" instrUnsignedRef },
    -- [B2] underflow path with an empty stack.
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "unit/underflow-empty" (runDICTISETGETSigned #[]) .stkUnd },
    -- [B2] underflow path with one stack cell.
    { name := "unit/runtime/underflow-one"
      run := do
        expectErr "unit/underflow-one" (runDICTISETGETSigned #[.slice valueA]) .stkUnd },
    -- [B2] underflow path with two stack cells.
    { name := "unit/runtime/underflow-two"
      run := do
        expectErr "unit/underflow-two" (runDICTISETGETSigned #[.slice valueA, .int (.num 1)]) .stkUnd },
    -- [B2] underflow path with three stack cells.
    { name := "unit/runtime/underflow-three"
      run := do
        expectErr "unit/underflow-three" (runDICTISETGETSigned #[.slice valueA, .int (.num 1), .cell dictSigned4]) .stkUnd },
    -- [B2] n argument range/type validation.
    { name := "unit/runtime/n-range-negative"
      run := do
        expectErr "unit/n-negative" (runDICTISETGETSigned (mkSignedStack valueA (-8) (.cell dictSigned4) (-1))) .rangeChk },
    -- [B2] n argument range/type validation.
    { name := "unit/runtime/n-range-too-large"
      run := do
        expectErr "unit/n-too-large" (runDICTISETGETSigned (mkSignedStack valueA 1 (.cell dictSigned4) 1024)) .rangeChk },
    -- [B2] n argument range/type validation.
    { name := "unit/runtime/n-range-nan"
      run := do
        expectErr "unit/n-nan" (runDICTISETGETSigned #[.slice valueA, .int (.num 1), .cell dictSigned4, .int .nan]) .rangeChk },
    -- [B3] signed key overflow conversion failure.
    { name := "unit/runtime/signed-key-high"
      run := do
        expectErr "unit/signed-key-high" (runDICTISETGETSigned (mkSignedStack valueA 8 (.cell dictSigned4) 4)) .rangeChk },
    -- [B3] signed key underflow conversion failure.
    { name := "unit/runtime/signed-key-low"
      run := do
        expectErr "unit/signed-key-low" (runDICTISETGETSigned (mkSignedStack valueA (-9) (.cell dictSigned4) 4)) .rangeChk },
    -- [B3] unsigned key negative conversion failure.
    { name := "unit/runtime/unsigned-key-negative"
      run := do
        expectErr "unit/unsigned-key-negative" (runDICTISETGETUnsigned (mkSignedStack valueA (-1) (.cell dictUnsigned4) 4)) .rangeChk },
    -- [B3] unsigned key overflow conversion failure.
    { name := "unit/runtime/unsigned-key-high"
      run := do
        expectErr "unit/unsigned-key-high" (runDICTISETGETUnsigned (mkSignedStack valueA 16 (.cell dictUnsigned4) 4)) .rangeChk },
    -- [B3] zero-width key-space rejects non-zero keys.
    { name := "unit/runtime/n0-key-non-zero"
      run := do
        expectErr "unit/n0-key-non-zero" (runDICTISETGETSigned (mkSignedStack valueA 1 (.cell dictSigned0) 0)) .rangeChk },
    -- [B4] runtime type errors (value/key/dict).
    { name := "unit/runtime/type-errors"
      run := do
        expectErr "unit/type-value" (runDICTISETGETSigned #[.int (.num 1), .int (.num 1), .cell dictSigned4, intV 4]) .typeChk
        expectErr "unit/type-key" (runDICTISETGETSigned #[.slice valueA, .slice valueB, .cell dictSigned4, intV 4]) .typeChk
        expectErr "unit/type-dict" (runDICTISETGETSigned (mkSignedStack valueA 1 (.tuple #[]) 4)) .typeChk },
    -- [B5] signed hit replacement returns old value and updated root.
    { name := "unit/runtime/semantics/signed-hit"
      run := do
        expectHitSliceShape "unit/signed-hit"
          (runDICTISETGETSigned (mkSignedStack valueE (-8) (.cell dictSigned4) 4))
          expectedReplaceSignedNeg8 },
    -- [B5] signed miss on empty dict inserts and returns zero.
    { name := "unit/runtime/semantics/signed-miss-null"
      run := do
        expectOkStack "unit/signed-miss-null"
          (runDICTISETGETSigned (mkSignedStack valueA 1 (.null) 4))
          #[.cell expectedInsertSigned1Null, intV 0] },
    -- [B5] signed miss on non-empty dict inserts and returns zero.
    { name := "unit/runtime/semantics/signed-miss-nonempty"
      run := do
        expectOkStack "unit/signed-miss-nonempty"
          (runDICTISETGETSigned (mkSignedStack valueB 1 (.cell dictSigned4) 4))
          #[.cell expectedInsertSigned1, intV 0] },
    -- [B3, B5] zero-width key-space successful replacement.
    { name := "unit/runtime/semantics/signed-n0"
      run := do
        expectHitSliceShape "unit/signed-n0"
          (runDICTISETGETSigned (mkSignedStack valueD 0 (.cell dictSigned0) 0))
          expectedSignedZeroWidth },
    -- [B5] unsigned hit replacement returns old value and updated root.
    { name := "unit/runtime/semantics/unsigned-hit"
      run := do
        expectHitSliceShape "unit/unsigned-hit"
          (runDICTISETGETUnsigned (mkSignedStack valueE 15 (.cell dictUnsigned4) 4))
          expectedReplaceUnsigned15 },
    -- [B5] unsigned miss on empty dict inserts and returns zero.
    { name := "unit/runtime/semantics/unsigned-miss-null"
      run := do
        expectOkStack "unit/unsigned-miss-null"
          (runDICTISETGETUnsigned (mkSignedStack valueC 3 (.null) 4))
          #[.cell expectedInsertUnsigned3Null, intV 0] },
    -- [B5] unsigned miss on non-empty dict inserts and returns zero.
    { name := "unit/runtime/semantics/unsigned-miss-nonempty"
      run := do
        expectOkStack "unit/unsigned-miss-nonempty"
          (runDICTISETGETUnsigned (mkSignedStack valueA 3 (.cell dictUnsigned4) 4))
          #[.cell expectedInsertUnsigned3, intV 0] },
    -- [B11, B5] by-ref hit replacement path.
    { name := "unit/runtime/semantics/ref-hit"
      run := do
        expectHitRefShape "unit/ref-hit"
          (runDICTISETGETRef (mkRefStack valueCellD 5 (.cell dictSigned4RefOk) 4))
          expectedReplaceRef5 },
    -- [B11, B5] by-ref miss-insert path.
    { name := "unit/runtime/semantics/ref-miss-null"
      run := do
        expectOkStack "unit/ref-miss-null"
          (runDICTISETGETRef (mkRefStack valueCellA 5 (.null) 4))
          #[.cell expectedInsertRefNull, intV 0] },
    -- [B6, B11] by-ref malformed payload shape rejects (bad remaining bits/refs).
    { name := "unit/runtime/ref-malformed-badbits"
      run := do
        expectErr "unit/ref-bad-bits" (runDICTISETGETRef (mkRefStack valueCellA 5 (.cell dictSigned4RefBadBits) 4)) .dictErr
        expectErr "unit/ref-bad-refs" (runDICTISETGETRef (mkRefStack valueCellA 5 (.cell dictSigned4RefBadRefs) 4)) .dictErr
        expectErr "unit/ref-no-ref" (runDICTISETGETRef (mkRefStack valueCellA 5 (.cell dictSigned4RefBadNoRef) 4)) .dictErr },
    -- [B6] malformed dictionary structure rejected as dictErr.
    { name := "unit/runtime/malformed-dict"
      run := do
        expectErr "unit/malformed-root-signed" (runDICTISETGETSigned (mkSignedStack valueA 5 (.cell malformedDict) 4)) .cellUnd
        expectErr "unit/malformed-root-unsigned" (runDICTISETGETUnsigned (mkSignedStack valueA 5 (.cell malformedDict) 4)) .cellUnd }
  ]
  oracle := #[
    -- [B2] underflow path with empty stack.
    mkCase "oracle/underflow-empty" #[],
    -- [B2] underflow path with one stack cell.
    mkCase "oracle/underflow-one" #[.slice valueA],
    -- [B2] underflow path with two stack cells.
    mkCase "oracle/underflow-two" #[.slice valueA, .int (.num 1)],
    -- [B2] underflow path with three stack cells.
    mkCase "oracle/underflow-three" #[.slice valueA, .int (.num 1), .cell dictSigned4],
    -- [B2] n argument range/type validation.
    mkCase "oracle/err/n-negative" (mkSignedStack valueA 1 (.cell dictSigned4) (-1)),
    -- [B2] n argument range/type validation.
    mkCase "oracle/err/n-too-large" (mkSignedStack valueA 1 (.cell dictSigned4) 1024),
    -- [B2] n argument range/type validation.
    mkCase "oracle/err/n-nan" #[.slice valueA, .int (.num 1), .cell dictSigned4, .int .nan],
    -- [B3] signed key overflow conversion failure.
    mkCase "oracle/err/signed-key-high" (mkSignedStack valueA 8 (.cell dictSigned4) 4),
    -- [B3] signed key underflow conversion failure.
    mkCase "oracle/err/signed-key-low" (mkSignedStack valueA (-9) (.cell dictSigned4) 4),
    -- [B3] unsigned key negative conversion failure.
    mkCodeCase "oracle/err/unsigned-key-negative" (mkSignedStack valueA (-1) (.cell dictUnsigned4) 4) rawF41E,
    -- [B3] unsigned key overflow conversion failure.
    mkCodeCase "oracle/err/unsigned-key-high" (mkSignedStack valueA 16 (.cell dictUnsigned4) 4) rawF41E,
    -- [B3] zero-width key-space rejects non-zero keys.
    mkCodeCase "oracle/err/n0-key-non-zero" (mkSignedStack valueA 1 (.cell dictSigned0) 0) rawF41C,
    -- [B4] value type must match slice/cell mode.
    mkCase "oracle/err/type-value" #[.int (.num 1), .int (.num 1), .cell dictSigned4, intV 4],
    -- [B4] key type must be int in signed/unsigned forms.
    mkCase "oracle/err/type-key" #[.slice valueA, .slice valueB, .cell dictSigned4, intV 4],
    -- [B4] dict root must be null or cell.
    mkCase "oracle/err/type-dict" (mkSignedStack valueA 1 (.tuple #[]) 4),
    -- [B6] malformed dictionary root rejected.
    mkCase "oracle/err/malformed-root-signed" (mkSignedStack valueA 1 (.cell malformedDict) 4),
    -- [B6] malformed dictionary root rejected.
    mkCodeCase "oracle/err/malformed-root-unsigned" (mkSignedStack valueA 1 (.cell malformedDict) 4) rawF41E,
    -- [B6, B11] by-ref malformed payload checks: remaining bits too large.
    mkCodeCase "oracle/err/ref-bad-bits" (mkRefStack valueCellA 5 (.cell dictSigned4RefBadBits) 4) rawF41D,
    -- [B6, B11] by-ref malformed payload checks: remaining refs must be exactly one.
    mkCodeCase "oracle/err/ref-bad-refs" (mkRefStack valueCellA 5 (.cell dictSigned4RefBadRefs) 4) rawF41D,
    -- [B6, B11] by-ref malformed payload checks: no refs to extract.
    mkCodeCase "oracle/err/ref-no-ref" (mkRefStack valueCellA 5 (.cell dictSigned4RefBadNoRef) 4) rawF41D,
    -- [B5] signed dict hit replacement.
    mkCase "oracle/ok/signed-hit" (mkSignedStack valueC (-8) (.cell dictSigned4) 4),
    -- [B5] signed dict miss insert into empty root.
    mkCase "oracle/ok/signed-miss-null" (mkSignedStack valueD 1 (.null) 4),
    -- [B5] signed dict miss insert into existing root.
    mkCase "oracle/ok/signed-miss-nonempty" (mkSignedStack valueB 1 (.cell dictSigned4) 4),
    -- [B3, B5] n=0 key-space edge success.
    mkCase "oracle/ok/signed-zero" (mkSignedStack valueA 0 (.cell dictSigned0) 0),
    -- [B5] unsigned dict hit replacement.
    mkCodeCase "oracle/ok/unsigned-hit" (mkSignedStack valueA 15 (.cell dictUnsigned4) 4) rawF41E,
    -- [B5] unsigned dict miss insert into empty root.
    mkCodeCase "oracle/ok/unsigned-miss-null" (mkSignedStack valueC 3 (.null) 4) rawF41E,
    -- [B5] unsigned dict miss insert into existing root.
    mkCodeCase "oracle/ok/unsigned-miss-nonempty" (mkSignedStack valueE 3 (.cell dictUnsigned4) 4) rawF41E,
    -- [B11, B5] by-ref hit replacement success.
    mkCodeCase "oracle/ok/ref-hit" (mkRefStack valueCellD 5 (.cell dictSigned4RefOk) 4) rawF41D,
    -- [B11, B5] by-ref miss insertion into empty dict.
    mkCodeCase "oracle/ok/ref-miss-null" (mkRefStack valueCellA 1 (.null) 4) rawF41D,
    -- [B8] decode/dispatch for opcode f41a.
    mkCodeCase "oracle/raw/f41a" (mkSignedStack valueA 0 (.cell dictSigned4) 4) rawF41A,
    -- [B8] decode/dispatch for opcode f41b.
    mkCodeCase "oracle/raw/f41b" (mkSignedStack valueA 0 (.cell dictSigned4) 4) rawF41B,
    -- [B8] decode/dispatch for opcode f41c.
    mkCodeCase "oracle/raw/f41c" (mkSignedStack valueA 0 (.cell dictSigned4) 4) rawF41C,
    -- [B8] decode/dispatch for opcode f41d.
    mkCodeCase "oracle/raw/f41d" (mkRefStack valueCellA 0 (.null) 4) rawF41D,
    -- [B8] decode/dispatch for opcode f41e.
    mkCodeCase "oracle/raw/f41e" (mkSignedStack valueA 0 (.null) 4) rawF41E,
    -- [B8] decode/dispatch for opcode f41f.
    mkCodeCase "oracle/raw/f41f" (mkRefStack valueCellA 0 (.null) 4) rawF41F,
    -- [B8] decode boundary case that must reject invOpcode.
    mkCodeCase "oracle/raw/f420" (mkSignedStack valueA 0 (.cell dictSigned4) 4) rawF420,
    -- [B8] decode truncated opcode width must reject invOpcode.
    mkCodeCase "oracle/raw/truncated-8" (mkSignedStack valueA 0 (.cell dictSigned4) 4) rawTrunc8,
    -- [B9] gas exact for signed hit path.
    mkGasCase "oracle/gas/exact/signed-hit" (mkSignedStack valueC (-8) (.cell dictSigned4) 4) rawF41C signedHitGas gasLimitsExactSignedHit,
    -- [B9] gas exact-minus-one for signed hit failure.
    mkGasCase "oracle/gas/exact-minus-one/signed-hit" (mkSignedStack valueC (-8) (.cell dictSigned4) 4) rawF41C signedHitGasMinusOne gasLimitsSignedHitMinusOne,
    -- [B9] gas exact for signed miss into null.
    mkGasCase "oracle/gas/exact/signed-miss-null" (mkSignedStack valueD 1 (.null) 4) rawF41C signedMissNullGas gasLimitsExactSignedMissNull,
    -- [B9] gas exact-minus-one for signed miss into null.
    mkGasCase "oracle/gas/exact-minus-one/signed-miss-null" (mkSignedStack valueD 1 (.null) 4) rawF41C signedMissNullGasMinusOne gasLimitsSignedMissNullMinusOne,
    -- [B9] gas exact for signed miss into non-empty root.
    mkGasCase "oracle/gas/exact/signed-miss-nonempty" (mkSignedStack valueB 1 (.cell dictSigned4) 4) rawF41C signedMissNonEmptyGas gasLimitsExactSignedMissNonEmpty,
    -- [B9] gas exact-minus-one for signed miss into non-empty root.
    mkGasCase "oracle/gas/exact-minus-one/signed-miss-nonempty" (mkSignedStack valueB 1 (.cell dictSigned4) 4) rawF41C signedMissNonEmptyGasMinusOne gasLimitsSignedMissNonEmptyMinusOne,
    -- [B9] gas exact for unsigned hit path.
    mkGasCase "oracle/gas/exact/unsigned-hit" (mkSignedStack valueA 15 (.cell dictUnsigned4) 4) rawF41E unsignedHitGas gasLimitsExactUnsignedHit,
    -- [B9] gas exact-minus-one for unsigned hit path.
    mkGasCase "oracle/gas/exact-minus-one/unsigned-hit" (mkSignedStack valueA 15 (.cell dictUnsigned4) 4) rawF41E unsignedHitGasMinusOne gasLimitsUnsignedHitMinusOne,
    -- [B9] gas exact for unsigned miss into null.
    mkGasCase "oracle/gas/exact/unsigned-miss" (mkSignedStack valueC 3 (.null) 4) rawF41E unsignedMissNullGas gasLimitsExactUnsignedMiss,
    -- [B9] gas exact-minus-one for unsigned miss into null.
    mkGasCase "oracle/gas/exact-minus-one/unsigned-miss" (mkSignedStack valueC 3 (.null) 4) rawF41E unsignedMissNullGasMinusOne gasLimitsUnsignedMissMinusOne
  ]
  -- [B10] explicit fuzzing drives remaining and implicit branches.
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTISETGETFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTISETGET
