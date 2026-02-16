import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUSETGETREF

/-!
INSTRUCTION: DICTUSETGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictExt` handles only `.dictExt` instructions and routes `.dictExt (.mutGet ... .set)` here.
   - Non-matching opcodes execute `next`.

2. [B2] Runtime arity and width validation.
   - `checkUnderflow 4` requires `[newValueRef, key, dict, n]`.
   - `n` is validated with `popNatUpTo 1023`, allowing only `0..1023`.
   - Negative / nan / out-of-range `n` yields `.rangeChk`.

3. [B3] Unsigned integer key conversion.
   - `key` is processed by `dictKeyBits?` with `unsigned = true`.
   - Out-of-range keys and keys outside `0..(2^n-1)` produce `.rangeChk`.
   - `n = 0` permits only key `0`.

4. [B4] Runtime type checks.
   - `newValue` must be a `.cell`.
   - `dict` must be `.null` or `.cell`.
   - `key` must be integer for unsigned integer key mode.

5. [B5] Runtime hit semantics.
   - In `.set` mode with existing key, returns `[newRoot, oldValueRef, -1]`.
   - Old entry is extracted by `extractRefOrThrow`.

6. [B6] Runtime miss semantics.
   - Inserting missing key returns `[newRoot, 0]`, works for `.null` and non-empty roots.

7. [B7] Ref payload shape and dictionary integrity.
   - `extractRefOrThrow` requires `bitsRemaining = 0` and `refsRemaining = 1`.
   - Bad shapes or malformed dictionaries cause `.dictErr`.

8. [B8] Assembler behavior.
   - `assembleCp0 [ .dictExt (...) ]` succeeds and roundtrips through `decodeCp0WithBits`.

9. [B9] Decoder behavior and opcode boundaries.
   - `0xF41A..0xF41F` are `dictExt` set/get families; `0xF41F` is this instruction.
   - `0xF419`, `0xF420`, and truncated `0xF4` must decode as `.invOpcode`.

10. [B10] Gas accounting.
   - Base gas is `computeExactGasBudget instr`.
   - `created` from mutation contributes `created * cellCreateGasPrice`.
   - Need exact-gas and exact-minus-one coverage for hit/miss branches.

TOTAL BRANCHES: 10

Every oracle test below is tagged [Bn] to branch coverage.
Any branch not covered by oracle tests MUST be covered by fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTUSETGETREF" }

private def instr : Instr :=
  .dictExt (.mutGet true true true .set)

private def dispatchSentinel : Int :=
  909

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def rawF41A : Cell := raw16 0xF41A
private def rawF41B : Cell := raw16 0xF41B
private def rawF41C : Cell := raw16 0xF41C
private def rawF41D : Cell := raw16 0xF41D
private def rawF41E : Cell := raw16 0xF41E
private def rawF41F : Cell := raw16 0xF41F
private def rawF419 : Cell := raw16 0xF419
private def rawF420 : Cell := raw16 0xF420
private def rawF4 : Cell := raw8 0xF4

private def valueCellA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueCellB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueCellC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def valueCellD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]
private def valueCellE : Cell := Cell.mkOrdinary (natToBits 0xE5 8) #[]
private def valueCellF : Cell := Cell.mkOrdinary (natToBits 0xF6 8) #[]
private def valueCellG : Cell := Cell.mkOrdinary (natToBits 0x77 8) #[]

private def valueSliceBadBits : Slice := mkSliceFromBits (natToBits 1 1)
private def valueSliceTwoRefs : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[valueCellA, valueCellB])
private def valueSliceNoRef : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[])
private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def bitsForUnsigned (label : String) (n : Nat) (key : Int) : BitString :=
  match dictKeyBits? key n true with
  | some bits => bits
  | none => panic! s!"{label}: invalid unsigned key {key} for n={n}"

private def mkDictSetRefBitsRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (bits, value) := entry
      match dictSetRefWithCells root bits value .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dict set by ref returned no root"
      | .error e =>
          panic! s!"{label}: dict set by ref failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict root"

private def mkDictSetSliceBitsRoot! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (bits, value) := entry
      match dictSetSliceWithCells root bits value .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dict set by slice returned no root"
      | .error e =>
          panic! s!"{label}: dict set by slice failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict root"

private def mkDictSetRefIntRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  mkDictSetRefBitsRoot! label (entries.map fun e => (bitsForUnsigned label n e.1, e.2))

private def mkDictSetSliceIntRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  mkDictSetSliceBitsRoot! label (entries.map fun e => (bitsForUnsigned label n e.1, e.2))

private def dict4 : Cell :=
  mkDictSetRefIntRoot! "DICTUSETGETREF/dict4" 4 #[(5, valueCellA), (12, valueCellB), (9, valueCellC)]

private def dict4NoTarget : Cell :=
  mkDictSetRefIntRoot! "DICTUSETGETREF/dict4NoTarget" 4 #[(0, valueCellD), (1, valueCellE), (7, valueCellF)]

private def dict0 : Cell :=
  mkDictSetRefIntRoot! "DICTUSETGETREF/dict0" 0 #[(0, valueCellA)]

private def dict1023 : Cell :=
  mkDictSetRefIntRoot! "DICTUSETGETREF/dict1023" 1023 #[(0, valueCellB)]

private def dictBadBits : Cell :=
  mkDictSetSliceIntRoot! "DICTUSETGETREF/dictBadBits" 4 #[(5, valueSliceBadBits)]

private def dictBadTwoRefs : Cell :=
  mkDictSetSliceIntRoot! "DICTUSETGETREF/dictBadTwoRefs" 4 #[(5, valueSliceTwoRefs)]

private def dictBadNoRef : Cell :=
  mkDictSetSliceIntRoot! "DICTUSETGETREF/dictBadNoRef" 4 #[(5, valueSliceNoRef)]

private def expectSetRoot
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (key : Int)
    (value : Cell) : Cell :=
  match dictLookupSetRefWithCells root (bitsForUnsigned label n key) value .set with
  | .ok (_, some newRoot, _ok, _created, _loaded) => newRoot
  | .ok (_, none, _ok, _created, _loaded) => panic! s!"{label}: expected new root, got none"
  | .error e => panic! s!"{label}: dictLookupSetRefWithCells failed ({reprStr e})"

private def expectSetCreated
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (key : Int)
    (value : Cell) : Nat :=
  match dictLookupSetRefWithCells root (bitsForUnsigned label n key) value .set with
  | .ok (_, _newRoot, _ok, created, _loaded) => created
  | .error e => panic! s!"{label}: dictLookupSetRefWithCells failed ({reprStr e})"

private def expectedHit4_5 : Cell :=
  expectSetRoot "DICTUSETGETREF/expected/hit/4/5" (some dict4) 4 5 valueCellD
private def expectedHit4_12 : Cell :=
  expectSetRoot "DICTUSETGETREF/expected/hit/4/12" (some dict4) 4 12 valueCellE
private def expectedHit0 : Cell :=
  expectSetRoot "DICTUSETGETREF/expected/hit/0" (some dict0) 0 0 valueCellC
private def expectedMiss4_2Null : Cell :=
  expectSetRoot "DICTUSETGETREF/expected/miss/4/2/null" none 4 2 valueCellA
private def expectedMiss4_2Pair : Cell :=
  expectSetRoot "DICTUSETGETREF/expected/miss/4/2/pair" (some dict4NoTarget) 4 2 valueCellB
private def expectedMiss1023 : Cell :=
  expectSetRoot "DICTUSETGETREF/expected/miss/1023" none 1023 0 valueCellF

private def createdHit4_5 : Nat :=
  expectSetCreated "DICTUSETGETREF/created/hit/4/5" (some dict4) 4 5 valueCellD
private def createdHit4_12 : Nat :=
  expectSetCreated "DICTUSETGETREF/created/hit/4/12" (some dict4) 4 12 valueCellE
private def createdHit0 : Nat :=
  expectSetCreated "DICTUSETGETREF/created/hit/0" (some dict0) 0 0 valueCellC
private def createdMiss4_2Null : Nat :=
  expectSetCreated "DICTUSETGETREF/created/miss/4/2/null" none 4 2 valueCellA
private def createdMiss4_2Pair : Nat :=
  expectSetCreated "DICTUSETGETREF/created/miss/4/2/pair" (some dict4NoTarget) 4 2 valueCellB
private def createdMiss1023 : Nat :=
  expectSetCreated "DICTUSETGETREF/created/miss/1023" none 1023 0 valueCellF

private def exactMinusOne (g : Int) : Int :=
  if g > 0 then g - 1 else 0

private def baseGas : Int :=
  computeExactGasBudget instr

private def exactGasHit4_5 : Int :=
  baseGas + Int.ofNat createdHit4_5 * cellCreateGasPrice
private def exactGasHit4_12 : Int :=
  baseGas + Int.ofNat createdHit4_12 * cellCreateGasPrice
private def exactGasMiss4_2Null : Int :=
  baseGas + Int.ofNat createdMiss4_2Null * cellCreateGasPrice
private def exactGasMiss4_2Pair : Int :=
  baseGas + Int.ofNat createdMiss4_2Pair * cellCreateGasPrice
private def exactGasHit0 : Int :=
  baseGas + Int.ofNat createdHit0 * cellCreateGasPrice
private def exactGasMiss1023 : Int :=
  baseGas + Int.ofNat createdMiss1023 * cellCreateGasPrice

private def exactGasHit4_5MinusOne : Int :=
  exactMinusOne exactGasHit4_5
private def exactGasHit4_12MinusOne : Int :=
  exactMinusOne exactGasHit4_12
private def exactGasMiss4_2NullMinusOne : Int :=
  exactMinusOne exactGasMiss4_2Null
private def exactGasMiss4_2PairMinusOne : Int :=
  exactMinusOne exactGasMiss4_2Pair
private def exactGasHit0MinusOne : Int :=
  exactMinusOne exactGasHit0
private def exactGasMiss1023MinusOne : Int :=
  exactMinusOne exactGasMiss1023

private def limitsExactHit4_5 : OracleGasLimits := oracleGasLimitsExact exactGasHit4_5
private def limitsExactHit4_12 : OracleGasLimits := oracleGasLimitsExact exactGasHit4_12
private def limitsExactMiss4_2Null : OracleGasLimits := oracleGasLimitsExact exactGasMiss4_2Null
private def limitsExactMiss4_2Pair : OracleGasLimits := oracleGasLimitsExact exactGasMiss4_2Pair
private def limitsExactHit0 : OracleGasLimits := oracleGasLimitsExact exactGasHit0
private def limitsExactMiss1023 : OracleGasLimits := oracleGasLimitsExact exactGasMiss1023
private def limitsExactMinusOneHit4_5 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasHit4_5MinusOne
private def limitsExactMinusOneHit4_12 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasHit4_12MinusOne
private def limitsExactMinusOneMiss4_2Null : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasMiss4_2NullMinusOne
private def limitsExactMinusOneMiss4_2Pair : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasMiss4_2PairMinusOne
private def limitsExactMinusOneHit0 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasHit0MinusOne
private def limitsExactMinusOneMiss1023 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasMiss1023MinusOne

private def gasLimitProgram (raw : Cell) (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok p =>
      Cell.mkOrdinary (p.bits ++ raw.bits) (p.refs ++ raw.refs)
  | .error e =>
      panic! s!"DICTUSETGETREF: gas program assembly failed ({reprStr e})"

private def mkStack (newValue : Cell) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[.cell newValue, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some rawF41F
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
    codeCell? := some (gasLimitProgram raw gas)
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecode (label : String) (rawCode : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell rawCode) with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed ({e})")
  | .ok (i, bits, rest) =>
      if i != expected || bits != 16 || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected {expected}, got {i} ({bits} bits, {rest.bitsRemaining}/{rest.refsRemaining})")

private def expectDecodeErr (label : String) (rawCode : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell rawCode) with
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} ({bits})")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected .invOpcode")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def expectAssembleOk16 (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assembly success, got {e}")
  | .ok raw =>
      expectDecode label raw i

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV dispatchSentinel)) stack

private def runDICTUSETGETREF (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def genDICTUSETGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 44
  let (tag, rng2) := randNat rng1 0 999_999
  let (base, rng3) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase "fuzz/err/underflow/empty" #[], rng2)
    else if shape = 1 then
      (mkCase "fuzz/err/underflow/one" #[.cell valueCellA], rng2)
    else if shape = 2 then
      (mkCase "fuzz/err/underflow/two" #[.cell valueCellA, .int (.num 1)], rng2)
    else if shape = 3 then
      (mkCase "fuzz/err/underflow/three" #[.cell valueCellA, .int (.num 1), .cell dict4], rng2)
    else if shape = 4 then
      (mkCase "fuzz/err/n-negative" (mkStack valueCellA 5 (.cell dict4) (-1)), rng2)
    else if shape = 5 then
      (mkCase "fuzz/err/n-too-large" (mkStack valueCellA 5 (.cell dict4) 1024), rng2)
    else if shape = 6 then
      (mkCase "fuzz/err/n-nan" #[.cell valueCellA, .int (.num 5), .cell dict4, .int .nan], rng2)
    else if shape = 7 then
      (mkCase "fuzz/err/key-negative" (mkStack valueCellA (-1) (.cell dict4) 4), rng2)
    else if shape = 8 then
      (mkCase "fuzz/err/key-too-large" (mkStack valueCellA 16 (.cell dict4) 4), rng2)
    else if shape = 9 then
      (mkCase "fuzz/err/key-nonzero-n0" (mkStack valueCellA 1 (.cell dict0) 0), rng2)
    else if shape = 10 then
      (mkCase "fuzz/err/type-value" (#[.int (.num 1), .int (.num 1), .cell dict4, intV 4]), rng2)
    else if shape = 11 then
      (mkCase "fuzz/err/type-key" (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4]), rng2)
    else if shape = 12 then
      (mkCase "fuzz/err/type-dict" (mkStack valueCellA 5 (.tuple #[]) 4), rng2)
    else if shape = 13 then
      (mkCase "fuzz/ok/hit/4/5" (mkStack valueCellD 5 (.cell dict4) 4), rng2)
    else if shape = 14 then
      (mkCase "fuzz/ok/hit/4/12" (mkStack valueCellE 12 (.cell dict4) 4), rng2)
    else if shape = 15 then
      (mkCase "fuzz/ok/hit/0/0" (mkStack valueCellC 0 (.cell dict0) 0), rng2)
    else if shape = 16 then
      (mkCase "fuzz/ok/miss/4/2-null" (mkStack valueCellA 2 (.null) 4), rng2)
    else if shape = 17 then
      (mkCase "fuzz/ok/miss/4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4), rng2)
    else if shape = 18 then
      (mkCase "fuzz/ok/miss/1023-null" (mkStack valueCellF 0 (.null) 1023), rng2)
    else if shape = 19 then
      (mkCodeCase "fuzz/alias/f41a" (mkStack valueCellA 0 (.cell dict4) 4) rawF41A, rng2)
    else if shape = 20 then
      (mkCodeCase "fuzz/alias/f41b" (mkStack valueCellB 1 (.cell dict4) 4) rawF41B, rng2)
    else if shape = 21 then
      (mkCodeCase "fuzz/alias/f41c" (mkStack valueCellC 2 (.cell dict4) 4) rawF41C, rng2)
    else if shape = 22 then
      (mkCodeCase "fuzz/alias/f41d" (mkStack valueCellD 3 (.cell dict4) 4) rawF41D, rng2)
    else if shape = 23 then
      (mkCodeCase "fuzz/alias/f41e" (mkStack valueCellE 4 (.cell dict4) 4) rawF41E, rng2)
    else if shape = 24 then
      (mkCodeCase "fuzz/alias/f41f" (mkStack valueCellF 5 (.cell dict4) 4) rawF41F, rng2)
    else if shape = 25 then
      (mkCodeCase "fuzz/err/gap/f419" (mkStack valueCellA 5 (.cell dict4) 4) rawF419, rng2)
    else if shape = 26 then
      (mkCodeCase "fuzz/err/gap/f420" (mkStack valueCellA 5 (.cell dict4) 4) rawF420, rng2)
    else if shape = 27 then
      (mkCodeCase "fuzz/err/gap/truncated" (mkStack valueCellA 5 (.cell dict4) 4) rawF4, rng2)
    else if shape = 28 then
      (mkCodeCase "fuzz/err/malformed-ref-bad-bits" (mkStack valueCellA 5 (.cell dictBadBits) 4) rawF41F, rng2)
    else if shape = 29 then
      (mkCodeCase "fuzz/err/malformed-ref-bad-refs" (mkStack valueCellA 5 (.cell dictBadTwoRefs) 4) rawF41F, rng2)
    else if shape = 30 then
      (mkCodeCase "fuzz/err/malformed-ref-no-ref" (mkStack valueCellA 5 (.cell dictBadNoRef) 4) rawF41F, rng2)
    else if shape = 31 then
      (mkCodeCase "fuzz/err/malformed-root" (mkStack valueCellA 5 (.cell malformedDictRoot) 4) rawF41F, rng2)
    else if shape = 32 then
      (mkGasCase "fuzz/gas/exact/hit-4/5" (mkStack valueCellD 5 (.cell dict4) 4) rawF41F exactGasHit4_5 limitsExactHit4_5, rng2)
    else if shape = 33 then
      (mkGasCase "fuzz/gas/exact-minus-one/hit-4/5" (mkStack valueCellD 5 (.cell dict4) 4) rawF41F exactGasHit4_5MinusOne limitsExactMinusOneHit4_5, rng2)
    else if shape = 34 then
      (mkGasCase "fuzz/gas/exact/hit-4/12" (mkStack valueCellE 12 (.cell dict4) 4) rawF41F exactGasHit4_12 limitsExactHit4_12, rng2)
    else if shape = 35 then
      (mkGasCase "fuzz/gas/exact-minus-one/hit-4/12" (mkStack valueCellE 12 (.cell dict4) 4) rawF41F exactGasHit4_12MinusOne limitsExactMinusOneHit4_12, rng2)
    else if shape = 36 then
      (mkGasCase "fuzz/gas/exact/miss-4/2-null" (mkStack valueCellA 2 (.null) 4) rawF41F exactGasMiss4_2Null limitsExactMiss4_2Null, rng2)
    else if shape = 37 then
      (mkGasCase "fuzz/gas/exact-minus-one/miss-4/2-null" (mkStack valueCellA 2 (.null) 4) rawF41F exactGasMiss4_2NullMinusOne limitsExactMinusOneMiss4_2Null, rng2)
    else if shape = 38 then
      (mkGasCase "fuzz/gas/exact/miss-4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4) rawF41F exactGasMiss4_2Pair limitsExactMiss4_2Pair, rng2)
    else if shape = 39 then
      (mkGasCase "fuzz/gas/exact-minus-one/miss-4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4) rawF41F exactGasMiss4_2PairMinusOne limitsExactMinusOneMiss4_2Pair, rng2)
    else if shape = 40 then
      (mkGasCase "fuzz/gas/exact/hit-0" (mkStack valueCellC 0 (.cell dict0) 0) rawF41F exactGasHit0 limitsExactHit0, rng2)
    else if shape = 41 then
      (mkGasCase "fuzz/gas/exact-minus-one/hit-0" (mkStack valueCellC 0 (.cell dict0) 0) rawF41F exactGasHit0MinusOne limitsExactMinusOneHit0, rng2)
    else if shape = 42 then
      (mkGasCase "fuzz/gas/exact/miss-1023" (mkStack valueCellF 0 (.null) 1023) rawF41F exactGasMiss1023 limitsExactMiss1023, rng2)
    else if shape = 43 then
      (mkGasCase "fuzz/gas/exact-minus-one/miss-1023" (mkStack valueCellF 0 (.null) 1023) rawF41F exactGasMiss1023MinusOne limitsExactMinusOneMiss1023, rng2)
    else
      (mkCodeCase (s!"fuzz/noise/{tag}") (mkStack valueCellG 7 (.cell dict4) 4) rawF41F, rng2)
  ({ base with name := s!"{base.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        let out := runDispatchFallback #[]
        expectOkStack "unit/dispatch/fallback" out #[intV dispatchSentinel] },
    { name := "unit/decoder/f41a"
      run := do
        expectDecode "unit/decoder/f41a" rawF41A (.dictExt (.mutGet false false false .set)) },
    { name := "unit/decoder/f41b"
      run := do
        expectDecode "unit/decoder/f41b" rawF41B (.dictExt (.mutGet false false true .set)) },
    { name := "unit/decoder/f41c"
      run := do
        expectDecode "unit/decoder/f41c" rawF41C (.dictExt (.mutGet true false false .set)) },
    { name := "unit/decoder/f41d"
      run := do
        expectDecode "unit/decoder/f41d" rawF41D (.dictExt (.mutGet true false true .set)) },
    { name := "unit/decoder/f41e"
      run := do
        expectDecode "unit/decoder/f41e" rawF41E (.dictExt (.mutGet true true false .set)) },
    { name := "unit/decoder/f41f"
      run := do
        expectDecode "unit/decoder/f41f" rawF41F (.dictExt (.mutGet true true true .set)) },
    { name := "unit/decoder/gaps"
      run := do
        expectDecodeErr "unit/decoder/gap/f419" rawF419
        expectDecodeErr "unit/decoder/gap/f420" rawF420
        expectDecodeErr "unit/decoder/gap/f4" rawF4 },
    { name := "unit/assemble/roundtrip"
      run := do
        expectAssembleOk16 "unit/assemble/roundtrip" instr },
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "unit/underflow-empty" (runDICTUSETGETREF #[]) .stkUnd },
    { name := "unit/runtime/underflow-one"
      run := do
        expectErr "unit/underflow-one" (runDICTUSETGETREF #[.cell valueCellA]) .stkUnd },
    { name := "unit/runtime/underflow-two"
      run := do
        expectErr "unit/underflow-two" (runDICTUSETGETREF #[.cell valueCellA, .int (.num 1)]) .stkUnd },
    { name := "unit/runtime/underflow-three"
      run := do
        expectErr "unit/underflow-three" (runDICTUSETGETREF #[.cell valueCellA, .int (.num 1), .cell dict4]) .stkUnd },
    { name := "unit/runtime/n-range-negative"
      run := do
        expectErr "unit/n-range-negative" (runDICTUSETGETREF (mkStack valueCellA 5 (.cell dict4) (-1))) .rangeChk },
    { name := "unit/runtime/n-range-too-large"
      run := do
        expectErr "unit/n-range-too-large" (runDICTUSETGETREF (mkStack valueCellA 5 (.cell dict4) 1024)) .rangeChk },
    { name := "unit/runtime/n-range-nan"
      run := do
        expectErr "unit/n-range-nan" (runDICTUSETGETREF #[.cell valueCellA, .int (.num 5), .cell dict4, .int .nan]) .rangeChk },
    { name := "unit/runtime/key-negative"
      run := do
        expectErr "unit/key-negative" (runDICTUSETGETREF (mkStack valueCellA (-1) (.cell dict4) 4)) .rangeChk },
    { name := "unit/runtime/key-too-large"
      run := do
        expectErr "unit/key-too-large" (runDICTUSETGETREF (mkStack valueCellA 16 (.cell dict4) 4)) .rangeChk },
    { name := "unit/runtime/key-nonzero-at-n0"
      run := do
        expectErr "unit/key-nonzero-at-n0" (runDICTUSETGETREF (mkStack valueCellA 1 (.cell dict0) 0)) .rangeChk },
    { name := "unit/runtime/type-errors"
      run := do
        expectErr "unit/type-value" (runDICTUSETGETREF (#[.int (.num 1), .int (.num 1), .cell dict4, intV 4])) .typeChk
        expectErr "unit/type-key" (runDICTUSETGETREF (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4])) .typeChk
        expectErr "unit/type-dict" (runDICTUSETGETREF (mkStack valueCellA 5 (.tuple #[]) 4)) .typeChk },
    { name := "unit/runtime/hit/4/5"
      run := do
        expectOkStack
          "unit/hit/4/5"
          (runDICTUSETGETREF (mkStack valueCellD 5 (.cell dict4) 4))
          #[.cell expectedHit4_5, .cell valueCellA, intV (-1)] },
    { name := "unit/runtime/hit/4/12"
      run := do
        expectOkStack
          "unit/hit/4/12"
          (runDICTUSETGETREF (mkStack valueCellE 12 (.cell dict4) 4))
          #[.cell expectedHit4_12, .cell valueCellB, intV (-1)] },
    { name := "unit/runtime/hit/0/0"
      run := do
        expectOkStack
          "unit/hit/0/0"
          (runDICTUSETGETREF (mkStack valueCellC 0 (.cell dict0) 0))
          #[.cell expectedHit0, .cell valueCellA, intV (-1)] },
    { name := "unit/runtime/miss/4/2-null"
      run := do
        expectOkStack
          "unit/miss/4/2-null"
          (runDICTUSETGETREF (mkStack valueCellA 2 (.null) 4))
          #[.cell expectedMiss4_2Null, intV 0] },
    { name := "unit/runtime/miss/4/2-pair"
      run := do
        expectOkStack
          "unit/miss/4/2-pair"
          (runDICTUSETGETREF (mkStack valueCellB 2 (.cell dict4NoTarget) 4))
          #[.cell expectedMiss4_2Pair, intV 0] },
    { name := "unit/runtime/miss/1023"
      run := do
        expectOkStack
          "unit/miss/1023"
          (runDICTUSETGETREF (mkStack valueCellF 0 (.null) 1023))
          #[.cell expectedMiss1023, intV 0] },
    { name := "unit/runtime/ref-shape-errors"
      run := do
        expectErr "unit/ref-bad-bits" (runDICTUSETGETREF (mkStack valueCellA 5 (.cell dictBadBits) 4)) .dictErr
        expectErr "unit/ref-bad-refs" (runDICTUSETGETREF (mkStack valueCellA 5 (.cell dictBadTwoRefs) 4)) .dictErr
        expectErr "unit/ref-no-ref" (runDICTUSETGETREF (mkStack valueCellA 5 (.cell dictBadNoRef) 4)) .dictErr },
    { name := "unit/runtime/malformed-root"
      run := do
        expectErr "unit/malformed-root" (runDICTUSETGETREF (mkStack valueCellA 5 (.cell malformedDictRoot) 4)) .cellUnd }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow-empty" #[],
    -- [B2]
    mkCase "oracle/underflow-one" #[.cell valueCellA],
    -- [B2]
    mkCase "oracle/underflow-two" #[.cell valueCellA, .int (.num 1)],
    -- [B2]
    mkCase "oracle/underflow-three" #[.cell valueCellA, .int (.num 1), .cell dict4],
    -- [B2][B3]
    mkCase "oracle/err/n-negative" (mkStack valueCellA 5 (.cell dict4) (-1)),
    -- [B2][B3]
    mkCase "oracle/err/n-too-large" (mkStack valueCellA 5 (.cell dict4) 1024),
    -- [B2][B3]
    mkCase "oracle/err/n-nan" #[.cell valueCellA, .int (.num 5), .cell dict4, .int .nan],
    -- [B3]
    mkCase "oracle/err/key-negative" (mkStack valueCellA (-1) (.cell dict4) 4),
    -- [B3]
    mkCase "oracle/err/key-too-large" (mkStack valueCellA 16 (.cell dict4) 4),
    -- [B3]
    mkCase "oracle/err/key-nonzero-n0" (mkStack valueCellA 1 (.cell dict0) 0),
    -- [B4]
    mkCase "oracle/err/type-value" (#[.int (.num 1), .int (.num 1), .cell dict4, intV 4]),
    -- [B4]
    mkCase "oracle/err/type-key" (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4]),
    -- [B4]
    mkCase "oracle/err/type-dict" (mkStack valueCellA 5 (.tuple #[]) 4),
    -- [B7]
    mkCase "oracle/err/malformed-root" (mkStack valueCellA 5 (.cell malformedDictRoot) 4),
    -- [B8]
    mkCodeCase "oracle/err/ref-bad-bits" (mkStack valueCellA 5 (.cell dictBadBits) 4) rawF41F,
    -- [B8]
    mkCodeCase "oracle/err/ref-bad-refs" (mkStack valueCellA 5 (.cell dictBadTwoRefs) 4) rawF41F,
    -- [B8]
    mkCodeCase "oracle/err/ref-no-ref" (mkStack valueCellA 5 (.cell dictBadNoRef) 4) rawF41F,
    -- [B6]
    mkCase "oracle/ok/hit/4/5" (mkStack valueCellD 5 (.cell dict4) 4),
    -- [B6]
    mkCase "oracle/ok/hit/4/12" (mkStack valueCellE 12 (.cell dict4) 4),
    -- [B6]
    mkCase "oracle/ok/hit/0/0" (mkStack valueCellC 0 (.cell dict0) 0),
    -- [B7]
    mkCase "oracle/ok/miss/4/2-null" (mkStack valueCellA 2 (.null) 4),
    -- [B7]
    mkCase "oracle/ok/miss/4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4),
    -- [B7]
    mkCase "oracle/ok/miss/1023-null" (mkStack valueCellF 0 (.null) 1023),
    -- [B1][B10]
    mkCodeCase "oracle/raw/f41a" (mkStack valueCellA 0 (.cell dict4) 4) rawF41A,
    -- [B1][B10]
    mkCodeCase "oracle/raw/f41b" (mkStack valueCellB 0 (.cell dict4) 4) rawF41B,
    -- [B1][B10]
    mkCodeCase "oracle/raw/f41c" (mkStack valueCellC 0 (.cell dict4) 4) rawF41C,
    -- [B1][B10]
    mkCodeCase "oracle/raw/f41d" (mkStack valueCellD 0 (.cell dict4) 4) rawF41D,
    -- [B1][B10]
    mkCodeCase "oracle/raw/f41e" (mkStack valueCellE 0 (.cell dict4) 4) rawF41E,
    -- [B1][B10]
    mkCodeCase "oracle/raw/f41f" (mkStack valueCellF 0 (.cell dict4) 4) rawF41F,
    -- [B9][B10]
    mkCodeCase "oracle/raw/f419" (mkStack valueCellA 0 (.cell dict4) 4) rawF419,
    -- [B9][B10]
    mkCodeCase "oracle/raw/f420" (mkStack valueCellA 0 (.cell dict4) 4) rawF420,
    -- [B9][B10]
    mkCodeCase "oracle/raw/f4" (mkStack valueCellA 0 (.cell dict4) 4) rawF4,
    -- [B10]
    mkGasCase "oracle/gas/exact/hit/4/5" (mkStack valueCellD 5 (.cell dict4) 4) rawF41F exactGasHit4_5 limitsExactHit4_5,
    -- [B10]
    mkGasCase "oracle/gas/exact-minus-one/hit/4/5" (mkStack valueCellD 5 (.cell dict4) 4) rawF41F exactGasHit4_5MinusOne limitsExactMinusOneHit4_5,
    -- [B10]
    mkGasCase "oracle/gas/exact/hit/4/12" (mkStack valueCellE 12 (.cell dict4) 4) rawF41F exactGasHit4_12 limitsExactHit4_12,
    -- [B10]
    mkGasCase "oracle/gas/exact-minus-one/hit/4/12" (mkStack valueCellE 12 (.cell dict4) 4) rawF41F exactGasHit4_12MinusOne limitsExactMinusOneHit4_12,
    -- [B10]
    mkGasCase "oracle/gas/exact/miss/4/2-null" (mkStack valueCellA 2 (.null) 4) rawF41F exactGasMiss4_2Null limitsExactMiss4_2Null,
    -- [B10]
    mkGasCase "oracle/gas/exact-minus-one/miss/4/2-null" (mkStack valueCellA 2 (.null) 4) rawF41F exactGasMiss4_2NullMinusOne limitsExactMinusOneMiss4_2Null,
    -- [B10]
    mkGasCase "oracle/gas/exact/miss/4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4) rawF41F exactGasMiss4_2Pair limitsExactMiss4_2Pair,
    -- [B10]
    mkGasCase "oracle/gas/exact-minus-one/miss/4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4) rawF41F exactGasMiss4_2PairMinusOne limitsExactMinusOneMiss4_2Pair,
    -- [B10]
    mkGasCase "oracle/gas/exact/hit/0" (mkStack valueCellC 0 (.cell dict0) 0) rawF41F exactGasHit0 limitsExactHit0,
    -- [B10]
    mkGasCase "oracle/gas/exact-minus-one/hit/0" (mkStack valueCellC 0 (.cell dict0) 0) rawF41F exactGasHit0MinusOne limitsExactMinusOneHit0,
    -- [B10]
    mkGasCase "oracle/gas/exact/miss/1023" (mkStack valueCellF 0 (.null) 1023) rawF41F exactGasMiss1023 limitsExactMiss1023,
    -- [B10]
    mkGasCase "oracle/gas/exact-minus-one/miss/1023" (mkStack valueCellF 0 (.null) 1023) rawF41F exactGasMiss1023MinusOne limitsExactMinusOneMiss1023
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTUSETGETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUSETGETREF
