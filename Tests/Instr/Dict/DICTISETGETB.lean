import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTISETGETB

/-
INSTRUCTION: DICTISETGETB

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch/fallback behavior.
   - `.dictExt (.mutGetB _ _ .set)` executes here.
   - Non-matching instructions must continue to `next`.

2. [B2] Stack/arith checks.
   - `checkUnderflow 4` requires builder, key, dict, and `n`.
   - `popNatUpTo 1023` enforces lower/upper bound of `n`.
   - Negative / NaN / out-of-range `n` all raise `.rangeChk`.

3. [B3] Slice key extraction.
   - Slice keys are read from top of stack and must provide `n` bits.
   - Short keys push `none` internally and then raise `.cellUnd` after validation.

4. [B4] Signed integer-key path.
   - `popInt` (may be `.nan`) plus `dictKeyBits?` with `unsigned = false`.
   - Invalid keys raise `.rangeChk`.

5. [B5] Unsigned integer-key path.
   - `popInt` (may be `.nan`) plus `dictKeyBits?` with `unsigned = true`.
   - Invalid keys and negatives raise `.rangeChk`.

6. [B6] Runtime success/fail result branches.
   - On hit, pushes previous value (slice) and `-1` for set-mode.
   - On miss, pushes `0` and updates root with inserted value.

7. [B7] Type checking.
   - Value must be a builder.
   - Dict may be `.null` or a cell; other values raise `.typeChk`.
   - Integer-key mode requires integer key value.

8. [B8] Dictionary traversal errors.
   - Malformed dictionary payload may raise `.dictErr`.
   - Visited cells are still tracked and registered by the VM.

9. [B9] Assembler behavior.
   - `.dictExt (.mutGetB _ _ .set)` encodes in CP0 assembler (opcodes `0xF445..0xF447`).

10. [B10] Decoder boundaries.
   - `0xF445`, `0xF446`, `0xF447` decode to `.mutGetB` set-builder variants.
   - Adjacent opcodes (`0xF444` / `0xF448`) and truncated `0xF4` decode as `.invOpcode`.

11. [B11] Gas accounting.
   - Base gas from `computeExactGasBudget`.
   - Exact and exact-minus-one checks must pass/fail along runtime branches.
   - Created-cell charge uses `created * cellCreateGasPrice`, so both empty and hit/update paths matter.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by fuzzer cases.
-/

private def suiteId : InstrId :=
  { name := "DICTISETGETB" }

private def instrSlice : Instr :=
  .dictExt (.mutGetB false false .set)

private def instrSigned : Instr :=
  .dictExt (.mutGetB true false .set)

private def instrUnsigned : Instr :=
  .dictExt (.mutGetB true true .set)

private def rawF445 : Cell :=
  Cell.mkOrdinary (natToBits 0xF445 16) #[]

private def rawF446 : Cell :=
  Cell.mkOrdinary (natToBits 0xF446 16) #[]

private def rawF447 : Cell :=
  Cell.mkOrdinary (natToBits 0xF447 16) #[]

private def rawF444 : Cell :=
  Cell.mkOrdinary (natToBits 0xF444 16) #[]

private def rawF448 : Cell :=
  Cell.mkOrdinary (natToBits 0xF448 16) #[]

private def rawTrunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def valueA : Builder :=
  Builder.empty.storeBits (natToBits 0xA1 8)

private def valueB : Builder :=
  Builder.empty.storeBits (natToBits 0xB2 8)

private def valueC : Builder :=
  Builder.empty.storeBits (natToBits 0xC3 8)

private def valueD : Builder :=
  Builder.empty.storeBits (natToBits 0xD4 8)

private def valueE : Builder :=
  Builder.empty.storeBits (natToBits 0xE5 8)

private def valueSliceA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueSliceB : Slice := mkSliceFromBits (natToBits 0xB2 8)

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkDictSetRoot! (label : String) (n : Nat) (unsigned : Bool)
    (entries : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n unsigned with
        | some bits => bits
        | none => panic! s!"{label}: cannot encode key {k} for n={n}, unsigned={unsigned}"
      match dictSetBuilderWithCells root keyBits v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root from set"
      | .error e =>
          panic! s!"{label}: dictSetBuilderWithCells failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"{label}: empty dictionary"

private def mkDictSetBitsRoot! (label : String) (entries : Array (BitString × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetBuilderWithCells root k v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root from set"
      | .error e =>
          panic! s!"{label}: dictSetBuilderWithCells failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"{label}: empty dictionary"

private def dictSlice4Single : Cell :=
  mkDictSetBitsRoot! "dictSlice4Single" #[
    (natToBits 0x3 4, valueA),
    (natToBits 0x7 4, valueB)
  ]

private def dictSlice4Miss : Cell :=
  mkDictSetBitsRoot! "dictSlice4Miss" #[
    (natToBits 0xA 4, valueA),
    (natToBits 0xC 4, valueB)
  ]

private def dictSlice8 : Cell :=
  mkDictSetBitsRoot! "dictSlice8" #[
    (natToBits 0x5A 8, valueA),
    (natToBits 0xC3 8, valueB),
    (natToBits 0x7A 8, valueC)
  ]

private def dictSlice0 : Cell :=
  mkDictSetBitsRoot! "dictSlice0" #[(#[], valueD)]

private def dictSigned4 : Cell :=
  mkDictSetRoot! "dictSigned4" 4 false #[
    (-8, valueA),
    (-1, valueB),
    (0, valueC),
    (7, valueD)
  ]

private def dictSigned8 : Cell :=
  mkDictSetRoot! "dictSigned8" 8 false #[
    (-128, valueA),
    (-1, valueB),
    (0, valueC),
    (127, valueD)
  ]

private def dictUnsigned4 : Cell :=
  mkDictSetRoot! "dictUnsigned4" 4 true #[
    (0, valueA),
    (1, valueB),
    (10, valueC),
    (15, valueD)
  ]

private def slice4A : Slice := mkSliceFromBits (natToBits 0x3 4)
private def slice4B : Slice := mkSliceFromBits (natToBits 0x7 4)
private def slice4C : Slice := mkSliceFromBits (natToBits 0x2 4)
private def slice4D : Slice := mkSliceFromBits (natToBits 0x1 4)
private def slice4Short : Slice := mkSliceFromBits (natToBits 0x1 1)
private def slice8A : Slice := mkSliceFromBits (natToBits 0x5A 8)
private def slice8B : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def slice8C : Slice := mkSliceFromBits (natToBits 0x7A 8)
private def slice8Miss : Slice := mkSliceFromBits (natToBits 0xFF 8)
private def slice0 : Slice := mkSliceFromBits #[]

private def keyBitsFor (label : String) (n : Nat) (unsigned : Bool) (k : Int) : BitString :=
  match dictKeyBits? k n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid key key={k}, n={n}, unsigned={unsigned}"

private def expectedSetReplaceSliceA : Cell :=
  match dictLookupSetBuilderWithCells (some dictSlice4Single) (natToBits 0x3 4) valueC .set with
  | .ok (_old, some root, _ok, _created, _loaded) => root
  | _ => dictSlice4Single

private def expectedSetReplaceSignedA : Cell :=
  match dictLookupSetBuilderWithCells (some dictSigned4) (keyBitsFor "expectedSetReplaceSignedA" 4 false (-8)) valueE .set with
  | .ok (_old, some root, _ok, _created, _loaded) => root
  | _ => dictSigned4

private def expectedSetReplaceUnsignedA : Cell :=
  match dictLookupSetBuilderWithCells (some dictUnsigned4) (keyBitsFor "expectedSetReplaceUnsignedA" 4 true 15) valueE .set with
  | .ok (_old, some root, _ok, _created, _loaded) => root
  | _ => dictUnsigned4

private def expectedSetNullSlice : Cell :=
  match dictLookupSetBuilderWithCells none (natToBits 0x1 4) valueB .set with
  | .ok (_old, some root, _ok, _created, _loaded) => root
  | _ => panic! "DICTISETGETB: unexpected root for empty-set baseline"

private def mkSliceStack (value : Builder) (key : Slice) (dict : Value := .null) (n : Int := 4) : Array Value :=
  #[.builder value, .slice key, dict, intV n]

private def mkIntStack (value : Builder) (key : Int) (dict : Value := .null) (n : Int := 4) : Array Value :=
  #[.builder value, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (instr : Instr := instrSlice)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[instr]
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

private def mkGasProgCase
    (name : String)
    (stack : Array Value)
    (instr : Instr)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]
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
  mkGasProgCase name stack instr gas gasLimits fuel

private def expectOkStack
    (label : String)
    (res : Except Excno (Array Value))
    (expected : Array Value) : IO Unit := do
  match res with
  | .ok st =>
      if st == expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr st}")
  | .error e =>
      throw (IO.userError s!"{label}: unexpected exception {e}")

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
  | .error e =>
      throw (IO.userError s!"{label}: expected assembly success, got {e}")
  | .ok code =>
      match decodeCp0WithBits (Slice.ofCell code) with
      | .error e =>
          throw (IO.userError s!"{label}: expected decode success, got {e}")
      | .ok (decoded, bits, rest) =>
          if decoded != instr then
            throw (IO.userError s!"{label}: expected {reprStr instr}, got {reprStr decoded}")
          else if bits != 16 then
            throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
          else if rest.bitsRemaining + rest.refsRemaining != 0 then
            throw (IO.userError s!"{label}: expected no trailing bits/refs")

private def expectDecodeInv (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} with {bits} bits")

private def createdBits (root : Option Cell) (key : BitString) (value : Builder) : Nat :=
  match dictLookupSetBuilderWithCells root key value .set with
  | .ok (_old, _new, _ok, created, _loaded) => created
  | .error e => panic! s!"DICTISETGETB: failed to precompute created cells ({reprStr e})"

private def createSliceMiss : Nat :=
  createdBits none (natToBits 0x1 4) valueB

private def createSliceHit : Nat :=
  createdBits (some dictSlice4Single) (natToBits 0x3 4) valueC

private def createSignedHit : Nat :=
  createdBits (some dictSigned4) (keyBitsFor "createSignedHit" 4 false (-8)) valueE

private def createUnsignedHit : Nat :=
  createdBits (some dictUnsigned4) (keyBitsFor "createUnsignedHit" 4 true 15) valueE

private def baseGasSlice : Int :=
  computeExactGasBudget instrSlice

private def baseGasSigned : Int :=
  computeExactGasBudget instrSigned

private def baseGasUnsigned : Int :=
  computeExactGasBudget instrUnsigned

private def missSliceGas : Int :=
  baseGasSlice + Int.ofNat createSliceMiss * cellCreateGasPrice

private def hitSliceGas : Int :=
  baseGasSlice + Int.ofNat createSliceHit * cellCreateGasPrice

private def signedGas : Int :=
  baseGasSigned + Int.ofNat createSignedHit * cellCreateGasPrice

private def unsignedGas : Int :=
  baseGasUnsigned + Int.ofNat createUnsignedHit * cellCreateGasPrice

private def missSliceGasMinusOne : Int :=
  if missSliceGas > 0 then missSliceGas - 1 else 0

private def hitSliceGasMinusOne : Int :=
  if hitSliceGas > 0 then hitSliceGas - 1 else 0

private def signedGasMinusOne : Int :=
  if signedGas > 0 then signedGas - 1 else 0

private def unsignedGasMinusOne : Int :=
  if unsignedGas > 0 then unsignedGas - 1 else 0

private def runDICTISETGETBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDICTISETGETBFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.tonEnvOp .setGasLimit) (VM.push (.int (.num 777))) stack

private def expectOkHitShape (label : String) (res : Except Excno (Array Value)) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.size != 3 then
        throw (IO.userError s!"{label}: expected 3 stack items, got {st.size}")
      match st[0]?, st[1]?, st[2]? with
      | some (Value.cell _), some (Value.slice _), some (Value.int (IntVal.num flag)) =>
          if flag != -1 then
            throw (IO.userError s!"{label}: expected success flag -1, got {flag}")
      | _, _, _ =>
          throw (IO.userError s!"{label}: unexpected stack shape {reprStr st}")

private def expectOkMissShape (label : String) (res : Except Excno (Array Value)) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.size != 2 then
        throw (IO.userError s!"{label}: expected 2 stack items, got {st.size}")
      match st[0]?, st[1]? with
      | some (Value.cell _), some (Value.int (IntVal.num flag)) =>
          if flag != 0 then
            throw (IO.userError s!"{label}: expected miss flag 0, got {flag}")
      | _, _ =>
          throw (IO.userError s!"{label}: unexpected stack shape {reprStr st}")

private def genDICTISETGETBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 42
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    match shape with
    | 0 =>
        (mkCase "fuzz/underflow/empty" #[], rng2)
    | 1 =>
        (mkCase "fuzz/underflow/one" #[.builder valueA], rng2)
    | 2 =>
        (mkCase "fuzz/underflow/two" (mkSliceStack valueA slice4A .null 4), rng2)
    | 3 =>
        (mkCase "fuzz/underflow/three" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4), rng2)
    | 4 =>
        (mkCase "fuzz/type/value-not-builder" (#[.int (.num 7), .slice slice4A, .cell dictSlice4Single, intV 4]), rng2)
    | 5 =>
        (mkCase "fuzz/slice/miss-null" (mkSliceStack valueA slice4B .null 4), rng2)
    | 6 =>
        (mkCase "fuzz/slice/hit" (mkSliceStack valueB slice4A (.cell dictSlice4Single) 4), rng2)
    | 7 =>
        (mkCase "fuzz/slice/hit8" (mkSliceStack valueC slice8A (.cell dictSlice8) 8), rng2)
    | 8 =>
        (mkCase "fuzz/slice/hit-zero" (mkSliceStack valueD slice0 (.cell dictSlice0) 0), rng2)
    | 9 =>
        (mkCase "fuzz/slice/miss-existing" (mkSliceStack valueA slice4C (.cell dictSlice4Miss) 4), rng2)
    | 10 =>
        (mkCase "fuzz/slice/key-short" (mkSliceStack valueA slice4Short (.cell dictSlice4Single) 4), rng2)
    | 11 =>
        (mkCase "fuzz/int/signed-hit" (mkIntStack valueA (-8) (.cell dictSigned4) 4) instrSigned, rng2)
    | 12 =>
        (mkCase "fuzz/int/signed-hit-alt" (mkIntStack valueB 7 (.cell dictSigned4) 4) instrSigned, rng2)
    | 13 =>
        (mkCase "fuzz/int/signed-miss" (mkIntStack valueC 1 (.cell dictSigned4) 4) instrSigned, rng2)
    | 14 =>
        (mkCase "fuzz/int/unsigned-hit" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) instrUnsigned, rng2)
    | 15 =>
        (mkCase "fuzz/int/unsigned-miss" (mkIntStack valueB 6 (.cell dictUnsigned4) 4) instrUnsigned, rng2)
    | 16 =>
        (mkCase "fuzz/int/unsigned-miss-null" (mkIntStack valueC 6 .null 4) instrUnsigned, rng2)
    | 17 =>
        (mkCase "fuzz/int/signed-out-of-range-high" (mkIntStack valueA 8 (.cell dictSigned4) 4) instrSigned, rng2)
    | 18 =>
        (mkCase "fuzz/int/signed-out-of-range-low" (mkIntStack valueA (-9) (.cell dictSigned4) 4) instrSigned, rng2)
    | 19 =>
        (mkCase "fuzz/int/unsigned-out-of-range" (mkIntStack valueA (-1) (.cell dictUnsigned4) 4) instrUnsigned, rng2)
    | 20 =>
        (mkCase "fuzz/n-negative" (mkSliceStack valueA slice4A (.cell dictSlice4Single) (-1)) , rng2)
    | 21 =>
        (mkCase "fuzz/n-too-large" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 1024), rng2)
    | 22 =>
        (mkCase "fuzz/n-nan" (#[.builder valueA, .slice slice4A, .cell dictSlice4Single, .int .nan]), rng2)
    | 23 =>
        (mkCase "fuzz/type/value" (#[.int (.num 1), .slice slice4A, .cell dictSlice4Single, intV 4]), rng2)
    | 24 =>
        (mkCase "fuzz/type/key" (mkSliceStack valueA slice4A (.cell dictSigned4) 4) instrSigned, rng2)
    | 25 =>
        (mkCase "fuzz/type/dict" (mkIntStack valueA 1 (.tuple #[]) 4), rng2)
    | 26 =>
        (mkCase "fuzz/malformed-root-slice" (mkSliceStack valueA slice4A (.cell malformedDict) 4), rng2)
    | 27 =>
        (mkCase "fuzz/malformed-root-int" (mkIntStack valueA 1 (.cell malformedDict) 4), rng2)
    | 28 =>
        (mkGasCase "fuzz/gas/slice-miss-exact" (mkSliceStack valueA slice4D .null 4) instrSlice missSliceGas (oracleGasLimitsExact missSliceGas), rng2)
    | 29 =>
        (mkGasCase "fuzz/gas/slice-miss-exact-minus-one" (mkSliceStack valueA slice4D .null 4) instrSlice missSliceGasMinusOne (oracleGasLimitsExactMinusOne missSliceGasMinusOne), rng2)
    | 30 =>
        (mkGasCase "fuzz/gas/slice-hit-exact" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4) instrSlice hitSliceGas (oracleGasLimitsExact hitSliceGas), rng2)
    | 31 =>
        (mkGasCase "fuzz/gas/slice-hit-exact-minus-one" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4) instrSlice hitSliceGasMinusOne (oracleGasLimitsExactMinusOne hitSliceGasMinusOne), rng2)
    | 32 =>
        (mkGasCase "fuzz/gas/signed-hit-exact" (mkIntStack valueA (-8) (.cell dictSigned4) 4) instrSigned signedGas (oracleGasLimitsExact signedGas), rng2)
    | 33 =>
        (mkGasCase "fuzz/gas/signed-hit-exact-minus-one" (mkIntStack valueA (-8) (.cell dictSigned4) 4) instrSigned signedGasMinusOne (oracleGasLimitsExactMinusOne signedGasMinusOne), rng2)
    | 34 =>
        (mkGasCase "fuzz/gas/unsigned-hit-exact" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) instrUnsigned unsignedGas (oracleGasLimitsExact unsignedGas), rng2)
    | 35 =>
        (mkGasCase "fuzz/gas/unsigned-hit-exact-minus-one" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) instrUnsigned unsignedGasMinusOne (oracleGasLimitsExactMinusOne unsignedGasMinusOne), rng2)
    | 36 =>
        (mkCodeCase "fuzz/decode/445" #[] rawF445, rng2)
    | 37 =>
        (mkCodeCase "fuzz/decode/446" #[] rawF446, rng2)
    | 38 =>
        (mkCodeCase "fuzz/decode/447" #[] rawF447, rng2)
    | 39 =>
        (mkCodeCase "fuzz/decode/444" #[] rawF444, rng2)
    | 40 =>
        (mkCodeCase "fuzz/decode/448" #[] rawF448, rng2)
    | 41 =>
        (mkCodeCase "fuzz/decode/trunc8" #[] rawTrunc8, rng2)
    | _ =>
        (mkCase "fuzz/range-noise" (mkSliceStack valueA slice4B .null 777), rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st := runDICTISETGETBFallback (mkIntStack valueA 0 (.cell dictSigned4) 4)
        let expected := mkIntStack valueA 0 (.cell dictSigned4) 4 ++ #[.int (.num 777)]
        expectOkStack "dispatch/fallback" st expected },
    { name := "unit/asm/encodes" -- [B9]
      run := do
        expectAssembleOk16 "asm/slice" instrSlice
        expectAssembleOk16 "asm/signed" instrSigned
        expectAssembleOk16 "asm/unsigned" instrUnsigned },
    { name := "unit/decode/valid" -- [B10]
      run := do
        let _ ← expectDecodeStep "decode/445" (Slice.ofCell rawF445) instrSlice 16
        let _ ← expectDecodeStep "decode/446" (Slice.ofCell rawF446) instrSigned 16
        let _ ← expectDecodeStep "decode/447" (Slice.ofCell rawF447) instrUnsigned 16 },
    { name := "unit/decode/invalid-adjacent-and-truncated" -- [B10]
      run := do
        expectDecodeInv "decode/444" rawF444
        expectDecodeInv "decode/448" rawF448
        expectDecodeInv "decode/trunc8" rawTrunc8 },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDICTISETGETBDirect instrSlice #[]) .stkUnd },
    { name := "unit/runtime/underflow-three" -- [B2]
      run := do
        expectErr "underflow-three" (runDICTISETGETBDirect instrSlice #[.builder valueA, .slice slice4A, .cell dictSlice4Single]) .stkUnd },
    { name := "unit/runtime/range-negative" -- [B2]
      run := do
        expectErr "n-negative" (runDICTISETGETBDirect instrSlice (mkSliceStack valueA slice4A (.cell dictSlice4Single) (-1))) .rangeChk },
    { name := "unit/runtime/range-too-large" -- [B2]
      run := do
        expectErr "n-too-large" (runDICTISETGETBDirect instrSlice (mkSliceStack valueA slice4A (.cell dictSlice4Single) 1024)) .rangeChk },
    { name := "unit/runtime/range-nan" -- [B2]
      run := do
        expectErr "n-nan" (runDICTISETGETBDirect instrSlice #[.builder valueA, .slice slice4A, .cell dictSlice4Single, .int .nan]) .rangeChk },
    { name := "unit/runtime/slice-key-short" -- [B3]
      run := do
        expectErr "slice-key-short" (runDICTISETGETBDirect instrSlice (mkSliceStack valueA slice4Short (.cell dictSlice4Single) 4)) .cellUnd },
    { name := "unit/runtime/int-key-range-signed" -- [B4]
      run := do
        expectErr "int-key-signed-high" (runDICTISETGETBDirect instrSigned (mkIntStack valueA 8 (.cell dictSigned4) 4)) .rangeChk
        expectErr "int-key-signed-low" (runDICTISETGETBDirect instrSigned (mkIntStack valueA (-9) (.cell dictSigned4) 4)) .rangeChk },
    { name := "unit/runtime/int-key-range-unsigned" -- [B5]
      run := do
        expectErr "int-key-unsigned" (runDICTISETGETBDirect instrUnsigned (mkIntStack valueA (-1) (.cell dictUnsigned4) 4)) .rangeChk },
    { name := "unit/runtime/type-errors" -- [B7]
      run := do
        expectErr "type-key" (runDICTISETGETBDirect instrSlice (mkIntStack valueA 1 (.cell dictSlice4Single) 4)) .typeChk
        expectErr "type-value" (runDICTISETGETBDirect instrSlice #[.int (.num 1), .slice slice4A, .cell dictSlice4Single, intV 4]) .typeChk
        expectErr "type-dict" (runDICTISETGETBDirect instrSigned (mkIntStack valueA 1 (.tuple #[]) 4)) .typeChk },
    { name := "unit/runtime/dict-malformed" -- [B8]
      run := do
        expectErr "dict-malformed-slice" (runDICTISETGETBDirect instrSlice (mkSliceStack valueA slice4A (.cell malformedDict) 4)) .cellUnd
        expectErr "dict-malformed-int" (runDICTISETGETBDirect instrSigned (mkIntStack valueA 1 (.cell malformedDict) 4)) .cellUnd },
    { name := "unit/runtime/set-hit-slice" -- [B6]
      run := do
        expectOkHitShape "set-hit-slice"
          (runDICTISETGETBDirect instrSlice (mkSliceStack valueC slice4A (.cell dictSlice4Single) 4)) },
    { name := "unit/runtime/set-hit-signed" -- [B6]
      run := do
        expectOkHitShape "set-hit-signed"
          (runDICTISETGETBDirect instrSigned (mkIntStack valueB (-8) (.cell dictSigned4) 4)) },
    { name := "unit/runtime/set-miss-signed-null" -- [B6]
      run := do
        expectOkMissShape "set-miss-null"
          (runDICTISETGETBDirect instrUnsigned (mkIntStack valueA 15 .null 4)) }
  ]
  oracle := #[
    mkCase "oracle/slice/hit" (mkSliceStack valueD slice4A (.cell dictSlice4Single) 4), -- [B3][B6]
    mkCase "oracle/slice/hit-8" (mkSliceStack valueD slice8B (.cell dictSlice8) 8), -- [B3][B6]
    mkCase "oracle/slice/hit-zero" (mkSliceStack valueA slice0 (.cell dictSlice0) 0), -- [B3][B6]
    mkCase "oracle/slice/miss-null" (mkSliceStack valueA slice4B .null 4), -- [B3][B6]
    mkCase "oracle/slice/miss-nonempty" (mkSliceStack valueA slice4D (.cell dictSlice4Miss) 4), -- [B3][B6]
    mkCase "oracle/slice/short" (mkSliceStack valueA slice4Short (.cell dictSlice4Single) 4), -- [B3][B6]

    mkCase "oracle/int/signed-hit-alt" (mkIntStack valueC (-8) (.cell dictSigned4) 4) instrSigned, -- [B4][B6]
    mkCase "oracle/int/signed-hit-max" (mkIntStack valueC 7 (.cell dictSigned4) 4) instrSigned, -- [B4][B6]
    mkCase "oracle/int/signed-miss" (mkIntStack valueD 6 (.cell dictSigned4) 4) instrSigned, -- [B6]
    mkCase "oracle/int/signed-miss-null" (mkIntStack valueD 6 .null 4) instrSigned, -- [B6]

    mkCase "oracle/int/unsigned-hit" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) instrUnsigned, -- [B5][B6]
    mkCase "oracle/int/unsigned-hit-zero" (mkIntStack valueA 0 (.cell dictUnsigned4) 4) instrUnsigned, -- [B5][B6]
    mkCase "oracle/int/unsigned-hit-one" (mkIntStack valueD 1 (.cell dictUnsigned4) 4) instrUnsigned, -- [B5][B6]
    mkCase "oracle/int/unsigned-miss" (mkIntStack valueB 6 (.cell dictUnsigned4) 4) instrUnsigned, -- [B6]

    mkCase "oracle/err/underflow/empty" #[], -- [B2]
    mkCase "oracle/err/underflow/one" #[.builder valueA], -- [B2]
    mkCase "oracle/err/underflow/two" (mkIntStack valueA 1 (.cell dictUnsigned4) 4), -- [B2]
    mkCase "oracle/err/underflow/three" (mkSliceStack valueA slice4A .null), -- [B2]

    mkCase "oracle/err/range/n-negative" (mkSliceStack valueA slice4A (.cell dictSlice4Single) (-1)), -- [B2]
    mkCase "oracle/err/range/n-too-large" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 1024), -- [B2]
    mkCase "oracle/err/range/n-nan" (#[.builder valueA, .slice slice4A, .cell dictSlice4Single, .int .nan]), -- [B2]

    mkCase "oracle/err/key-nan" (#[.builder valueA, .int .nan, .cell dictSigned4, intV 4]), -- [B4]
    mkCase "oracle/err/type-key-slice" (mkSliceStack valueA slice4A (.cell dictSigned4) 4), -- [B7]
    mkCase "oracle/err/type-key-not-int" (mkSliceStack valueA slice4A (.cell dictSigned4) 4), -- [B7]
    mkCase "oracle/err/value-not-builder" (#[.int (.num 1), .slice slice4A, .cell dictSlice4Single, intV 4]), -- [B7]
    mkCase "oracle/err/dict-not-cell" (mkIntStack valueA 1 (.tuple #[]) 4) instrSigned, -- [B7]

    mkCase "oracle/err/key-int-out-of-range-low" (mkIntStack valueA (-9) (.cell dictSigned4) 4) instrSigned, -- [B4]
    mkCase "oracle/err/key-int-out-of-range-high" (mkIntStack valueA 8 (.cell dictSigned4) 4) instrSigned, -- [B4]
    mkCase "oracle/err/key-uint-out-of-range-low" (mkIntStack valueA (-1) (.cell dictUnsigned4) 4) instrUnsigned, -- [B5]

    mkCase "oracle/err/malformed-root-slice" (mkSliceStack valueA slice4A (.cell malformedDict) 4), -- [B8]
    mkCase "oracle/err/malformed-root-int" (mkIntStack valueA 1 (.cell malformedDict) 4) instrSigned, -- [B8]

    mkCodeCase "oracle/code/445" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4) rawF445, -- [B10]
    mkCodeCase "oracle/code/446" (mkIntStack valueA (-8) (.cell dictSigned4) 4) rawF446, -- [B10]
    mkCodeCase "oracle/code/447" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) rawF447, -- [B10]
    mkCodeCase "oracle/code/invalid-444" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4) rawF444, -- [B10]
    mkCodeCase "oracle/code/invalid-448" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4) rawF448, -- [B10]
    mkCodeCase "oracle/code/invalid-trunc8" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4) rawTrunc8, -- [B10]

    mkGasCase "oracle/gas/slice-miss-exact" (mkSliceStack valueA slice4D .null 4) instrSlice missSliceGas (oracleGasLimitsExact missSliceGas), -- [B11]
    mkGasCase "oracle/gas/slice-miss-minus-one" (mkSliceStack valueA slice4D .null 4) instrSlice missSliceGasMinusOne (oracleGasLimitsExactMinusOne missSliceGasMinusOne), -- [B11]
    mkGasCase "oracle/gas/slice-hit-exact" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4) instrSlice hitSliceGas (oracleGasLimitsExact hitSliceGas), -- [B11]
    mkGasCase "oracle/gas/slice-hit-minus-one" (mkSliceStack valueA slice4A (.cell dictSlice4Single) 4) instrSlice hitSliceGasMinusOne (oracleGasLimitsExactMinusOne hitSliceGasMinusOne), -- [B11]
    mkGasCase "oracle/gas/signed-exact" (mkIntStack valueA (-8) (.cell dictSigned4) 4) instrSigned signedGas (oracleGasLimitsExact signedGas), -- [B11]
    mkGasCase "oracle/gas/signed-minus-one" (mkIntStack valueA (-8) (.cell dictSigned4) 4) instrSigned signedGasMinusOne (oracleGasLimitsExactMinusOne signedGasMinusOne), -- [B11]
    mkGasCase "oracle/gas/unsigned-exact" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) instrUnsigned unsignedGas (oracleGasLimitsExact unsignedGas), -- [B11]
    mkGasCase "oracle/gas/unsigned-minus-one" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) instrUnsigned unsignedGasMinusOne (oracleGasLimitsExactMinusOne unsignedGasMinusOne) -- [B11]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTISETGETBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTISETGETB
