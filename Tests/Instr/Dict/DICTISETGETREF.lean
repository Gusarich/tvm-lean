import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTISETGETREF

/-!
INSTRUCTION: DICTISETGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch branch.
   - `execInstrDictExt` only handles `.dictExt` opcodes. Non-matching instructions must continue via `next`.
   - We verify this via `runHandlerDirectWithNext` fallback behavior.

2. [B2] Runtime arity and `n` range.
   - `checkUnderflow 4` is required before reading `newValue`, `key`, `dict`, and `n`.
   - `popNatUpTo 1023` validates `n`; negative/NaN/above-1023 causes `.rangeChk`.

3. [B3] Signed integer key conversion.
   - `dictKeyBits?` runs in signed mode (`unsigned = false`).
   - Valid keys satisfy `-2^(n-1) <= key < 2^(n-1)` with `n = 0` allowing only key `0`.
   - Violations in key range yield `.rangeChk`.

4. [B4] Runtime typing.
   - `newValue` must be `.cell` (by-ref mode), `key` must be integer, `dict` must be `null` or `.cell`.
   - Type errors are surfaced as `.typeChk` on normal stack pop order.

5. [B5] Runtime hit path (.set semantics).
   - On hit, dictionary root is updated.
   - Old stored value is extracted as exactly one reference with no remaining bits.
   - Stack becomes `[newRoot, oldValue, -1]`.

6. [B6] Runtime miss path (.set semantics).
   - On miss, dictionary root is updated with inserted key/value pair.
   - Returned boolean indicates miss with `0`.
   - Stack becomes `[newRoot, 0]`.

7. [B7] Ref-shape and dictionary integrity validation.
   - `extractRefOrThrow` validates old value shape; non-ref or malformed payload gives `.dictErr`.
   - Malformed dictionary roots may also produce `.dictErr`.

8. [B8] Assembler/decoder behavior.
   - 16-bit decoder range is `0xF43A..0xF43F`.
   - `0xF439`, `0xF440`, and truncated `0xF4` must be `.invOpcode`.
   - `.dictExt` for this family is assembler-unsupported (`.invOpcode`).

9. [B9] Gas accounting.
   - Base gas from `computeExactGasBudget instr`.
   - Mutations add `created * cellCreateGasPrice` to gas limit for both hit and miss.
   - Exact-gas-success and exact-gas-minus-one branches are exercised.

10. [B10] Branch-by-branch opcode alias coverage.
    - `0xF43A..0xF43F` cover the full signed/unsigned/byRef SETGETREF family with mode `.set`.
    - `runDICTISETGETREF` uses explicit `codeCell?` cases to ensure all aliases are observed.

TOTAL BRANCHES: 10

Every oracle test below is tagged [Bn] to branch coverage.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTISETGETREF" }

private def instr : Instr :=
  .dictExt (.mutGet true false true .set)

private def dispatchSentinel : Int :=
  909

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawF43A : Cell := raw16 0xF43A
private def rawF43B : Cell := raw16 0xF43B
private def rawF43C : Cell := raw16 0xF43C
private def rawF43D : Cell := raw16 0xF43D
private def rawF43E : Cell := raw16 0xF43E
private def rawF43F : Cell := raw16 0xF43F
private def rawF439 : Cell := raw16 0xF439
private def rawF440 : Cell := raw16 0xF440
private def rawF4 : Cell := raw16 0xF4

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

private def bitsForSigned (label : String) (n : Nat) (key : Int) : BitString :=
  match dictKeyBits? key n false with
  | some bits => bits
  | none => panic! s!"{label}: invalid signed key {key} for n={n}"

private def mkDictSetRefBitsRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (bits, value) := entry
      match dictSetRefWithCells root bits value .set with
      | .ok (some nextRoot, _ok, _created, _loaded) =>
          root := nextRoot
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
      | .ok (some nextRoot, _ok, _created, _loaded) =>
          root := nextRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dict set by slice returned no root"
      | .error e =>
          panic! s!"{label}: dict set by slice failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict root"

private def mkDictSetRefIntRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  mkDictSetRefBitsRoot! label (entries.map fun e => (bitsForSigned label n e.1, e.2))

private def mkDictSetSliceIntRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  mkDictSetSliceBitsRoot! label (entries.map fun e => (bitsForSigned label n e.1, e.2))

private def dict4 : Cell :=
  mkDictSetRefIntRoot! "DICTISETGETREF/dict4" 4 #[(5, valueCellA), (-4, valueCellB), (3, valueCellC)]

private def dict4NoTarget : Cell :=
  mkDictSetRefIntRoot! "DICTISETGETREF/dict4NoTarget" 4 #[(0, valueCellD), (-1, valueCellE), (-2, valueCellF)]

private def dict0 : Cell :=
  mkDictSetRefIntRoot! "DICTISETGETREF/dict0" 0 #[(0, valueCellA)]

private def dict1023 : Cell :=
  mkDictSetRefIntRoot! "DICTISETGETREF/dict1023" 1023 #[(0, valueCellB)]

private def dictBadBits : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGETREF/dictBadBits" 4 #[(5, valueSliceBadBits)]

private def dictBadTwoRefs : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGETREF/dictBadTwoRefs" 4 #[(5, valueSliceTwoRefs)]

private def dictBadNoRef : Cell :=
  mkDictSetSliceIntRoot! "DICTISETGETREF/dictBadNoRef" 4 #[(5, valueSliceNoRef)]

private def expectSetRoot
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (key : Int)
    (value : Cell) : Cell :=
  match dictLookupSetRefWithCells root (bitsForSigned label n key) value .set with
  | .ok (_, some newRoot, _ok, _created, _loaded) => newRoot
  | .ok (_, none, _ok, _created, _loaded) => panic! s!"{label}: expected new root, got none"
  | .error e => panic! s!"{label}: dictLookupSetRefWithCells failed ({reprStr e})"

private def expectSetCreated
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (key : Int)
    (value : Cell) : Nat :=
  match dictLookupSetRefWithCells root (bitsForSigned label n key) value .set with
  | .ok (_, _newRoot, _ok, created, _loaded) => created
  | .error e => panic! s!"{label}: dictLookupSetRefWithCells failed ({reprStr e})"

private def expectedHit4_5 : Cell :=
  expectSetRoot "DICTISETGETREF/expected/hit/4/5" (some dict4) 4 5 valueCellD
private def expectedHit4_neg4 : Cell :=
  expectSetRoot "DICTISETGETREF/expected/hit/4/-4" (some dict4) 4 (-4) valueCellE
private def expectedHit4_3 : Cell :=
  expectSetRoot "DICTISETGETREF/expected/hit/4/3" (some dict4) 4 3 valueCellF
private def expectedHit0 : Cell :=
  expectSetRoot "DICTISETGETREF/expected/hit/0" (some dict0) 0 0 valueCellD
private def expectedMiss4_2Null : Cell :=
  expectSetRoot "DICTISETGETREF/expected/miss/4/2/null" none 4 2 valueCellA
private def expectedMiss4_2Pair : Cell :=
  expectSetRoot "DICTISETGETREF/expected/miss/4/2/pair" (some dict4NoTarget) 4 2 valueCellB
private def expectedMiss1023 : Cell :=
  expectSetRoot "DICTISETGETREF/expected/miss/1023" none 1023 0 valueCellF

private def createdHit4_5 : Nat :=
  expectSetCreated "DICTISETGETREF/created/hit/4/5" (some dict4) 4 5 valueCellD
private def createdHit4_neg4 : Nat :=
  expectSetCreated "DICTISETGETREF/created/hit/4/-4" (some dict4) 4 (-4) valueCellE
private def createdHit4_3 : Nat :=
  expectSetCreated "DICTISETGETREF/created/hit/4/3" (some dict4) 4 3 valueCellF
private def createdHit0 : Nat :=
  expectSetCreated "DICTISETGETREF/created/hit/0" (some dict0) 0 0 valueCellD
private def createdMiss4_2Null : Nat :=
  expectSetCreated "DICTISETGETREF/created/miss/4/2/null" none 4 2 valueCellA
private def createdMiss4_2Pair : Nat :=
  expectSetCreated "DICTISETGETREF/created/miss/4/2/pair" (some dict4NoTarget) 4 2 valueCellB
private def createdMiss1023 : Nat :=
  expectSetCreated "DICTISETGETREF/created/miss/1023" none 1023 0 valueCellF

private def exactMinusOne (g : Int) : Int :=
  if g > 0 then g - 1 else 0

private def baseGas : Int :=
  computeExactGasBudget instr

private def exactGasHit4_5 : Int :=
  baseGas + Int.ofNat createdHit4_5 * cellCreateGasPrice
private def exactGasHit4_neg4 : Int :=
  baseGas + Int.ofNat createdHit4_neg4 * cellCreateGasPrice
private def exactGasHit4_3 : Int :=
  baseGas + Int.ofNat createdHit4_3 * cellCreateGasPrice
private def exactGasHit0 : Int :=
  baseGas + Int.ofNat createdHit0 * cellCreateGasPrice
private def exactGasMiss4_2Null : Int :=
  baseGas + Int.ofNat createdMiss4_2Null * cellCreateGasPrice
private def exactGasMiss4_2Pair : Int :=
  baseGas + Int.ofNat createdMiss4_2Pair * cellCreateGasPrice
private def exactGasMiss1023 : Int :=
  baseGas + Int.ofNat createdMiss1023 * cellCreateGasPrice

private def exactGasHit4_5MinusOne : Int :=
  exactMinusOne exactGasHit4_5
private def exactGasHit4_neg4MinusOne : Int :=
  exactMinusOne exactGasHit4_neg4
private def exactGasHit4_3MinusOne : Int :=
  exactMinusOne exactGasHit4_3
private def exactGasHit0MinusOne : Int :=
  exactMinusOne exactGasHit0
private def exactGasMiss4_2NullMinusOne : Int :=
  exactMinusOne exactGasMiss4_2Null
private def exactGasMiss4_2PairMinusOne : Int :=
  exactMinusOne exactGasMiss4_2Pair
private def exactGasMiss1023MinusOne : Int :=
  exactMinusOne exactGasMiss1023

private def limitsExactHit4_5 : OracleGasLimits := oracleGasLimitsExact exactGasHit4_5
private def limitsExactHit4_neg4 : OracleGasLimits := oracleGasLimitsExact exactGasHit4_neg4
private def limitsExactHit4_3 : OracleGasLimits := oracleGasLimitsExact exactGasHit4_3
private def limitsExactHit0 : OracleGasLimits := oracleGasLimitsExact exactGasHit0
private def limitsExactMiss4_2Null : OracleGasLimits := oracleGasLimitsExact exactGasMiss4_2Null
private def limitsExactMiss4_2Pair : OracleGasLimits := oracleGasLimitsExact exactGasMiss4_2Pair
private def limitsExactMiss1023 : OracleGasLimits := oracleGasLimitsExact exactGasMiss1023
private def limitsExactMinusOneHit4_5 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasHit4_5MinusOne
private def limitsExactMinusOneHit4_neg4 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasHit4_neg4MinusOne
private def limitsExactMinusOneHit4_3 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasHit4_3MinusOne
private def limitsExactMinusOneHit0 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasHit0MinusOne
private def limitsExactMinusOneMiss4_2Null : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasMiss4_2NullMinusOne
private def limitsExactMinusOneMiss4_2Pair : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasMiss4_2PairMinusOne
private def limitsExactMinusOneMiss1023 : OracleGasLimits := oracleGasLimitsExactMinusOne exactGasMiss1023MinusOne

private def gasLimitProgram (raw : Cell) (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok p =>
      Cell.mkOrdinary (p.bits ++ raw.bits) (p.refs ++ raw.refs)
  | .error e =>
      panic! s!"DICTISETGETREF: gas program assembly failed ({reprStr e})"

private def mkStack (newValue : Cell) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[.cell newValue, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some rawF43D
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
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected .invOpcode")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.dictGet false false false) (VM.push (.int (.num dispatchSentinel))) stack

private def runDICTISETGETREF (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def genDICTISETGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 44
  let (tag, rng2) := randNat rng1 0 999_999
  let (base, rng3) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase (s!"fuzz/err/underflow-empty/{tag}") #[], rng2)
    else if shape = 1 then
      (mkCase (s!"fuzz/err/underflow-one/{tag}") #[.cell valueCellA], rng2)
    else if shape = 2 then
      (mkCase (s!"fuzz/err/underflow-two/{tag}") #[.cell valueCellA, .int (.num 1)], rng2)
    else if shape = 3 then
      (mkCase (s!"fuzz/err/underflow-three/{tag}") #[.cell valueCellA, .int (.num 1), .cell dict4], rng2)
    else if shape = 4 then
      (mkCase (s!"fuzz/err/n-negative/{tag}") (mkStack valueCellA 5 (.cell dict4) (-1)), rng2)
    else if shape = 5 then
      (mkCase (s!"fuzz/err/n-too-large/{tag}") (mkStack valueCellA 5 (.cell dict4) 1024), rng2)
    else if shape = 6 then
      (mkCase (s!"fuzz/err/n-nan/{tag}") (#[.cell valueCellA, .int (.num 5), .cell dict4, .int .nan]), rng2)
    else if shape = 7 then
      (mkCase (s!"fuzz/err/key-negative/{tag}") (mkStack valueCellA (-9) (.cell dict4) 4), rng2)
    else if shape = 8 then
      (mkCase (s!"fuzz/err/key-too-large/{tag}") (mkStack valueCellA 8 (.cell dict4) 4), rng2)
    else if shape = 9 then
      (mkCase (s!"fuzz/err/key-nonzero-at-n0/{tag}") (mkStack valueCellA 1 (.cell dict0) 0), rng2)
    else if shape = 10 then
      (mkCase (s!"fuzz/err/type-value/{tag}") (#[.int (.num 7), .int (.num 5), .cell dict4, intV 4]), rng2)
    else if shape = 11 then
      (mkCase (s!"fuzz/err/type-key/{tag}") (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4]), rng2)
    else if shape = 12 then
      (mkCase (s!"fuzz/err/type-dict/{tag}") (mkStack valueCellA 5 (.tuple #[]) 4), rng2)
    else if shape = 13 then
      (mkCase (s!"fuzz/ok/hit/4/5/{tag}") (mkStack valueCellD 5 (.cell dict4) 4), rng2)
    else if shape = 14 then
      (mkCase (s!"fuzz/ok/hit/4/-4/{tag}") (mkStack valueCellE (-4) (.cell dict4) 4), rng2)
    else if shape = 15 then
      (mkCase (s!"fuzz/ok/hit/4/3/{tag}") (mkStack valueCellF 3 (.cell dict4) 4), rng2)
    else if shape = 16 then
      (mkCase (s!"fuzz/ok/hit/0/0/{tag}") (mkStack valueCellD 0 (.cell dict0) 0), rng2)
    else if shape = 17 then
      (mkCase (s!"fuzz/ok/miss/4/2/null/{tag}") (mkStack valueCellA 2 (.null) 4), rng2)
    else if shape = 18 then
      (mkCase (s!"fuzz/ok/miss/4/2/pair/{tag}") (mkStack valueCellB 2 (.cell dict4NoTarget) 4), rng2)
    else if shape = 19 then
      (mkCase (s!"fuzz/ok/miss/1023/null/{tag}") (mkStack valueCellF 0 (.null) 1023), rng2)
    else if shape = 20 then
      (mkCase (s!"fuzz/ok/miss/wide/null/{tag}") (mkStack valueCellA 0 (.null) 257), rng2)
    else if shape = 21 then
      (mkCodeCase (s!"fuzz/raw/f43a/{tag}") (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4]) rawF43A, rng2)
    else if shape = 22 then
      (mkCodeCase (s!"fuzz/raw/f43b/{tag}") (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4]) rawF43B, rng2)
    else if shape = 23 then
      (mkCodeCase (s!"fuzz/raw/f43c/{tag}") (mkStack valueCellA 5 (.cell dict4) 4) rawF43C, rng2)
    else if shape = 24 then
      (mkCodeCase (s!"fuzz/raw/f43d/{tag}") (mkStack valueCellA 5 (.cell dict4) 4) rawF43D, rng2)
    else if shape = 25 then
      (mkCodeCase (s!"fuzz/raw/f43e/{tag}") (mkStack valueCellA 5 (.cell dict4) 4) rawF43E, rng2)
    else if shape = 26 then
      (mkCodeCase (s!"fuzz/raw/f43f/{tag}") (mkStack valueCellA 5 (.cell dict4) 4) rawF43F, rng2)
    else if shape = 27 then
      (mkCodeCase (s!"fuzz/err/raw/f439/{tag}") (mkStack valueCellA 5 (.cell dict4) 4) rawF439, rng2)
    else if shape = 28 then
      (mkCodeCase (s!"fuzz/err/raw/f440/{tag}") (mkStack valueCellA 5 (.cell dict4) 4) rawF440, rng2)
    else if shape = 29 then
      (mkCodeCase (s!"fuzz/err/raw/f4/{tag}") (mkStack valueCellA 5 (.cell dict4) 4) rawF4, rng2)
    else if shape = 30 then
      (mkCodeCase (s!"fuzz/err/ref-bits/{tag}") (mkStack valueCellA 5 (.cell dictBadBits) 4) rawF43D, rng2)
    else if shape = 31 then
      (mkCodeCase (s!"fuzz/err/ref-two-refs/{tag}") (mkStack valueCellA 5 (.cell dictBadTwoRefs) 4) rawF43D, rng2)
    else if shape = 32 then
      (mkCodeCase (s!"fuzz/err/ref-no-ref/{tag}") (mkStack valueCellA 5 (.cell dictBadNoRef) 4) rawF43D, rng2)
    else if shape = 33 then
      (mkCodeCase (s!"fuzz/err/malformed-root/{tag}") (mkStack valueCellA 5 (.cell malformedDictRoot) 4) rawF43D, rng2)
    else if shape = 34 then
      (mkGasCase
        (s!"fuzz/gas/exact/hit/4/5/{tag}")
        (mkStack valueCellD 5 (.cell dict4) 4)
        rawF43D
        exactGasHit4_5
        limitsExactHit4_5,
        rng2)
    else if shape = 35 then
      (mkGasCase
        (s!"fuzz/gas/exact-minus-one/hit/4/5/{tag}")
        (mkStack valueCellD 5 (.cell dict4) 4)
        rawF43D
        exactGasHit4_5MinusOne
        limitsExactMinusOneHit4_5,
        rng2)
    else if shape = 36 then
      (mkGasCase
        (s!"fuzz/gas/exact/miss/4/2/null/{tag}")
        (mkStack valueCellA 2 (.null) 4)
        rawF43D
        exactGasMiss4_2Null
        limitsExactMiss4_2Null,
        rng2)
    else if shape = 37 then
      (mkGasCase
        (s!"fuzz/gas/exact-minus-one/miss/4/2/null/{tag}")
        (mkStack valueCellA 2 (.null) 4)
        rawF43D
        exactGasMiss4_2NullMinusOne
        limitsExactMinusOneMiss4_2Null,
        rng2)
    else if shape = 38 then
      (mkGasCase
        (s!"fuzz/gas/exact/hit/4/3/{tag}")
        (mkStack valueCellF 3 (.cell dict4) 4)
        rawF43D
        exactGasHit4_3
        limitsExactHit4_3,
        rng2)
    else if shape = 39 then
      (mkGasCase
        (s!"fuzz/gas/exact-minus-one/hit/4/3/{tag}")
        (mkStack valueCellF 3 (.cell dict4) 4)
        rawF43D
        exactGasHit4_3MinusOne
        limitsExactMinusOneHit4_3,
        rng2)
    else if shape = 40 then
      (mkGasCase
        (s!"fuzz/gas/exact/miss/1023/{tag}")
        (mkStack valueCellF 0 (.null) 1023)
        rawF43D
        exactGasMiss1023
        limitsExactMiss1023,
        rng2)
    else if shape = 41 then
      (mkGasCase
        (s!"fuzz/gas/exact-minus-one/miss/1023/{tag}")
        (mkStack valueCellF 0 (.null) 1023)
        rawF43D
        exactGasMiss1023MinusOne
        limitsExactMinusOneMiss1023,
        rng2)
    else if shape = 42 then
      (mkCodeCase (s!"fuzz/trim-stack/{tag}") (#[.int (.num 777), .cell valueCellB, intV 5, .cell dict4, intV 4]) rawF43D, rng2)
    else if shape = 43 then
      (mkCase (s!"fuzz/ok/hit/4/-4/more/{tag}") (mkStack valueCellE (-4) (.cell dict4) 4), rng2)
    else if shape = 44 then
      (mkCase (s!"fuzz/noise/{tag}") (mkStack valueCellG 2 (.cell dict4) 4), rng2)
    else
      (mkCase (s!"fuzz/fallback/{tag}") (mkStack valueCellA 5 (.cell dict4) 4), rng2)
  ({ base with name := base.name }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let out := runDispatchFallback #[]
        expectOkStack "unit/dispatch/fallback" out #[intV dispatchSentinel] },
    { name := "unit/decoder/f43a" -- [B8][B10]
      run := do
        expectDecode "unit/decoder/f43a" rawF43A (.dictExt (.mutGet false false false .set))
    },
    { name := "unit/decoder/f43b" -- [B8][B10]
      run := do
        expectDecode "unit/decoder/f43b" rawF43B (.dictExt (.mutGet false false true .set))
    },
    { name := "unit/decoder/f43c" -- [B8][B10]
      run := do
        expectDecode "unit/decoder/f43c" rawF43C (.dictExt (.mutGet true false false .set))
    },
    { name := "unit/decoder/f43d" -- [B8][B10]
      run := do
        expectDecode "unit/decoder/f43d" rawF43D (.dictExt (.mutGet true false true .set))
    },
    { name := "unit/decoder/f43e" -- [B8][B10]
      run := do
        expectDecode "unit/decoder/f43e" rawF43E (.dictExt (.mutGet true true false .set))
    },
    { name := "unit/decoder/f43f" -- [B8][B10]
      run := do
        expectDecode "unit/decoder/f43f" rawF43F (.dictExt (.mutGet true true true .set))
    },
    { name := "unit/decoder/gaps" -- [B8][B10]
      run := do
        expectDecodeErr "unit/decoder/gap/f439" rawF439
        expectDecodeErr "unit/decoder/gap/f440" rawF440
        expectDecodeErr "unit/decoder/gap/f4" rawF4
    },
    { name := "unit/asm/unsupported" -- [B8]
      run := do
        expectAssembleInvOpcode "unit/asm/unsupported" instr
    },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "unit/runtime/underflow-empty" (runDICTISETGETREF #[]) .stkUnd
    },
    { name := "unit/runtime/underflow-one" -- [B2]
      run := do
        expectErr "unit/runtime/underflow-one" (runDICTISETGETREF #[.cell valueCellA]) .stkUnd
    },
    { name := "unit/runtime/underflow-two" -- [B2]
      run := do
        expectErr "unit/runtime/underflow-two" (runDICTISETGETREF #[.cell valueCellA, .int (.num 1)]) .stkUnd
    },
    { name := "unit/runtime/underflow-three" -- [B2]
      run := do
        expectErr "unit/runtime/underflow-three" (runDICTISETGETREF #[.cell valueCellA, .int (.num 1), .cell dict4]) .stkUnd
    },
    { name := "unit/runtime/n-range-negative" -- [B3]
      run := do
        expectErr "unit/runtime/n-range-negative" (runDICTISETGETREF (mkStack valueCellA 5 (.cell dict4) (-1))) .rangeChk
    },
    { name := "unit/runtime/n-range-too-large" -- [B3]
      run := do
        expectErr "unit/runtime/n-range-too-large" (runDICTISETGETREF (mkStack valueCellA 5 (.cell dict4) 1024)) .rangeChk
    },
    { name := "unit/runtime/n-range-nan" -- [B3]
      run := do
        expectErr "unit/runtime/n-range-nan" (runDICTISETGETREF (#[.cell valueCellA, .int (.num 5), .cell dict4, .int .nan])) .rangeChk
    },
    { name := "unit/runtime/key-range-negative" -- [B3]
      run := do
        expectErr "unit/runtime/key-range-negative" (runDICTISETGETREF (mkStack valueCellA (-9) (.cell dict4) 4)) .rangeChk
    },
    { name := "unit/runtime/key-range-high" -- [B3]
      run := do
        expectErr "unit/runtime/key-range-high" (runDICTISETGETREF (mkStack valueCellA 8 (.cell dict4) 4)) .rangeChk
    },
    { name := "unit/runtime/key-range-nonzero-n0" -- [B3]
      run := do
        expectErr "unit/runtime/key-range-nonzero-n0" (runDICTISETGETREF (mkStack valueCellA 1 (.cell dict0) 0)) .rangeChk
    },
    { name := "unit/runtime/type-value" -- [B4]
      run := do
        expectErr "unit/runtime/type-value" (runDICTISETGETREF (#[.int (.num 7), .int (.num 5), .cell dict4, intV 4])) .typeChk
    },
    { name := "unit/runtime/type-key" -- [B4]
      run := do
        expectErr "unit/runtime/type-key" (runDICTISETGETREF (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4])) .typeChk
    },
    { name := "unit/runtime/type-dict" -- [B4]
      run := do
        expectErr "unit/runtime/type-dict" (runDICTISETGETREF (mkStack valueCellA 5 (.tuple #[]) 4)) .typeChk
    },
    { name := "unit/runtime/hit/4/5" -- [B5]
      run := do
        expectOkStack
          "unit/runtime/hit/4/5"
          (runDICTISETGETREF (mkStack valueCellD 5 (.cell dict4) 4))
          #[.cell expectedHit4_5, .cell valueCellA, intV (-1)]
    },
    { name := "unit/runtime/hit/4/-4" -- [B5]
      run := do
        expectOkStack
          "unit/runtime/hit/4/-4"
          (runDICTISETGETREF (mkStack valueCellE (-4) (.cell dict4) 4))
          #[.cell expectedHit4_neg4, .cell valueCellB, intV (-1)]
    },
    { name := "unit/runtime/hit/0/0" -- [B5]
      run := do
        expectOkStack
          "unit/runtime/hit/0/0"
          (runDICTISETGETREF (mkStack valueCellD 0 (.cell dict0) 0))
          #[.cell expectedHit0, .cell valueCellA, intV (-1)]
    },
    { name := "unit/runtime/miss/4/2-null" -- [B6]
      run := do
        expectOkStack
          "unit/runtime/miss/4/2-null"
          (runDICTISETGETREF (mkStack valueCellA 2 (.null) 4))
          #[.cell expectedMiss4_2Null, intV 0]
    },
    { name := "unit/runtime/miss/4/2-pair" -- [B6]
      run := do
        expectOkStack
          "unit/runtime/miss/4/2-pair"
          (runDICTISETGETREF (mkStack valueCellB 2 (.cell dict4NoTarget) 4))
          #[.cell expectedMiss4_2Pair, intV 0]
    },
    { name := "unit/runtime/miss/1023" -- [B6]
      run := do
        expectOkStack
          "unit/runtime/miss/1023"
          (runDICTISETGETREF (mkStack valueCellF 0 (.null) 1023))
          #[.cell expectedMiss1023, intV 0]
    },
    { name := "unit/runtime/ref-shape-errors" -- [B7]
      run := do
        expectErr "unit/runtime/ref-bits" (runDICTISETGETREF (mkStack valueCellA 5 (.cell dictBadBits) 4)) .dictErr
        expectErr "unit/runtime/ref-two-refs" (runDICTISETGETREF (mkStack valueCellA 5 (.cell dictBadTwoRefs) 4)) .dictErr
        expectErr "unit/runtime/ref-no-ref" (runDICTISETGETREF (mkStack valueCellA 5 (.cell dictBadNoRef) 4)) .dictErr
    },
    { name := "unit/runtime/malformed-root" -- [B7]
      run := do
        expectErr "unit/runtime/malformed-root" (runDICTISETGETREF (mkStack valueCellA 5 (.cell malformedDictRoot) 4)) .dictErr
    }
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
    -- [B3]
    mkCase "oracle/err/n-negative" (mkStack valueCellA 5 (.cell dict4) (-1)),
    -- [B3]
    mkCase "oracle/err/n-too-large" (mkStack valueCellA 5 (.cell dict4) 1024),
    -- [B3]
    mkCase "oracle/err/n-nan" (#[.cell valueCellA, .int (.num 5), .cell dict4, .int .nan]),
    -- [B3]
    mkCase "oracle/err/key-negative" (mkStack valueCellA (-9) (.cell dict4) 4),
    -- [B3]
    mkCase "oracle/err/key-too-large" (mkStack valueCellA 8 (.cell dict4) 4),
    -- [B3]
    mkCase "oracle/err/key-nonzero-n0" (mkStack valueCellA 1 (.cell dict0) 0),
    -- [B4]
    mkCase "oracle/err/type-value" (#[.int (.num 7), .int (.num 5), .cell dict4, intV 4]),
    -- [B4]
    mkCase "oracle/err/type-key" (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4]),
    -- [B4]
    mkCase "oracle/err/type-dict" (mkStack valueCellA 5 (.tuple #[]) 4),
    -- [B7]
    mkCodeCase "oracle/err/raw/f439" #[] rawF439,
    -- [B7]
    mkCodeCase "oracle/err/raw/f440" #[] rawF440,
    -- [B7]
    mkCodeCase "oracle/err/raw/f4" #[] rawF4,
    -- [B7]
    mkCodeCase "oracle/err/ref-bad-bits" (mkStack valueCellA 5 (.cell dictBadBits) 4) rawF43D,
    -- [B7]
    mkCodeCase "oracle/err/ref-bad-refs" (mkStack valueCellA 5 (.cell dictBadTwoRefs) 4) rawF43D,
    -- [B7]
    mkCodeCase "oracle/err/ref-no-ref" (mkStack valueCellA 5 (.cell dictBadNoRef) 4) rawF43D,
    -- [B7]
    mkCase "oracle/err/malformed-root" (mkStack valueCellA 5 (.cell malformedDictRoot) 4),
    -- [B5]
    mkCase "oracle/ok/hit/4/5" (mkStack valueCellD 5 (.cell dict4) 4),
    -- [B5]
    mkCase "oracle/ok/hit/4/-4" (mkStack valueCellE (-4) (.cell dict4) 4),
    -- [B5]
    mkCase "oracle/ok/hit/4/3" (mkStack valueCellF 3 (.cell dict4) 4),
    -- [B5]
    mkCase "oracle/ok/hit/0/0" (mkStack valueCellD 0 (.cell dict0) 0),
    -- [B6]
    mkCase "oracle/ok/miss/4/2-null" (mkStack valueCellA 2 (.null) 4),
    -- [B6]
    mkCase "oracle/ok/miss/4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4),
    -- [B6]
    mkCase "oracle/ok/miss/1023" (mkStack valueCellF 0 (.null) 1023),
    -- [B10]
    mkCodeCase "oracle/raw/f43a" (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4]) rawF43A,
    -- [B10]
    mkCodeCase "oracle/raw/f43b" (#[.cell valueCellA, .slice valueSliceBadBits, .cell dict4, intV 4]) rawF43B,
    -- [B10]
    mkCodeCase "oracle/raw/f43c" (mkStack valueCellA 5 (.cell dict4) 4) rawF43C,
    -- [B10]
    mkCodeCase "oracle/raw/f43d" (mkStack valueCellA 5 (.cell dict4) 4) rawF43D,
    -- [B10]
    mkCodeCase "oracle/raw/f43e" (mkStack valueCellA 5 (.cell dict4) 4) rawF43E,
    -- [B10]
    mkCodeCase "oracle/raw/f43f" (mkStack valueCellA 5 (.cell dict4) 4) rawF43F,
    -- [B9]
    mkGasCase "oracle/gas/exact/hit/4/5" (mkStack valueCellD 5 (.cell dict4) 4) rawF43D exactGasHit4_5 limitsExactHit4_5,
    -- [B9]
    mkGasCase "oracle/gas/exact-minus-one/hit/4/5" (mkStack valueCellD 5 (.cell dict4) 4) rawF43D exactGasHit4_5MinusOne limitsExactMinusOneHit4_5,
    -- [B9]
    mkGasCase "oracle/gas/exact/miss/4/2-null" (mkStack valueCellA 2 (.null) 4) rawF43D exactGasMiss4_2Null limitsExactMiss4_2Null,
    -- [B9]
    mkGasCase "oracle/gas/exact-minus-one/miss/4/2-null" (mkStack valueCellA 2 (.null) 4) rawF43D exactGasMiss4_2NullMinusOne limitsExactMinusOneMiss4_2Null,
    -- [B9]
    mkGasCase "oracle/gas/exact/miss/4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4) rawF43D exactGasMiss4_2Pair limitsExactMiss4_2Pair,
    -- [B9]
    mkGasCase "oracle/gas/exact-minus-one/miss/4/2-pair" (mkStack valueCellB 2 (.cell dict4NoTarget) 4) rawF43D exactGasMiss4_2PairMinusOne limitsExactMinusOneMiss4_2Pair,
    -- [B9]
    mkGasCase "oracle/gas/exact/hit/4/3" (mkStack valueCellF 3 (.cell dict4) 4) rawF43D exactGasHit4_3 limitsExactHit4_3,
    -- [B9]
    mkGasCase "oracle/gas/exact-minus-one/hit/4/3" (mkStack valueCellF 3 (.cell dict4) 4) rawF43D exactGasHit4_3MinusOne limitsExactMinusOneHit4_3,
    -- [B9]
    mkGasCase "oracle/gas/exact/hit/0" (mkStack valueCellD 0 (.cell dict0) 0) rawF43D exactGasHit0 limitsExactHit0,
    -- [B9]
    mkGasCase "oracle/gas/exact-minus-one/hit/0" (mkStack valueCellD 0 (.cell dict0) 0) rawF43D exactGasHit0MinusOne limitsExactMinusOneHit0,
    -- [B9]
    mkGasCase "oracle/gas/exact/miss/1023" (mkStack valueCellF 0 (.null) 1023) rawF43D exactGasMiss1023 limitsExactMiss1023,
    -- [B9]
    mkGasCase "oracle/gas/exact-minus-one/miss/1023" (mkStack valueCellF 0 (.null) 1023) rawF43D exactGasMiss1023MinusOne limitsExactMinusOneMiss1023
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTISETGETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTISETGETREF
