import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUSETGET

/-!
INSTRUCTION: DICTUSETGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `execInstrDictExt` handles `.dictExt (.mutGet true true false .set)`.
   - All other instruction variants and malformed opcode sequences follow `.next`/`decode` paths outside this handler.

2. [B2] Runtime arity check.
   - `checkUnderflow 4` is mandatory.
   - Empty stack, one-item, two-item, and three-item stacks must fail with `.stkUnd`.

3. [B3] Width operand validation (`n`).
   - `popNatUpTo 1023` accepts `0..1023` only.
   - Negative/NaN/`>1023` values raise `.rangeChk`.
   - `n = 0` is valid when used with exact integer key conversion.

4. [B4] Unsigned integer-key conversion semantics.
   - Key is read with `popInt` and converted using `dictKeyBits? idx n true` via `Lean.dictKeyBits?`.
   - `.nan` immediately maps to `.rangeChk`.
   - Out-of-range keys (`idx < 0` or `idx >= 2^n`) are `.rangeChk`.
   - For `n = 0`, only key `0` is valid.

5. [B5] Argument typing order and checks.
   - Arguments are consumed as: `newValue(slice), key(int), dict(maybe-cell), n(int)`.
   - New value must be a slice; dict must be `null` or cell; key must be integer in this mode.

6. [B6] Runtime set-hit semantics.
   - Valid existing key performs `dictLookupSetSliceWithCells` and returns
     `[new_root, old_value, -1]`.
   - Hit path does not return a raw `0` success flag.

7. [B7] Runtime miss semantics.
   - Missing key on empty or non-empty root returns `[new_root, 0]`.
   - `old_value` is absent on miss.

8. [B8] Malformed dictionary root / corrupted payload behavior.
   - Malformed root cells propagate as `.dictErr` when mutation/traversal attempts to parse labels.

9. [B9] Decoder encoding boundaries and aliases.
   - `0xF43A..0xF43F` decode as DICTUSETGET family variants (`mutGet` set mode),
     with `intKey` and `unsigned` bits varying by low opcode bits.
   - `0xF439` and `0xF440` are `.invOpcode` gaps.
   - `0xF4` is truncated/too-short and decodes as `.invOpcode`.

10. [B10] Assembler behavior.
   - CP0 assembler encodes this opcode family (16-bit opcodes).

11. [B11] Gas accounting.
   - There is a fixed opcode base component (`computeExactGasBudget`).
   - Runtime path additionally consumes `cellCreateGasPrice * created`.
   - Exact and exact-minus-one limits must be covered for both hit and miss mutation branches.

TOTAL BRANCHES: 11

Every oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTUSETGET" }

private def instr : Instr := .dictExt (.mutGet true true false .set)

private def raw16 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 16) #[]
private def raw8 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 8) #[]

private def rawF43A : Cell := raw16 0xF43A
private def rawF43B : Cell := raw16 0xF43B
private def rawF43C : Cell := raw16 0xF43C
private def rawF43D : Cell := raw16 0xF43D
private def rawF43E : Cell := raw16 0xF43E
private def rawF43F : Cell := raw16 0xF43F
private def rawF439 : Cell := raw16 0xF439
private def rawF440 : Cell := raw16 0xF440
private def rawF4 : Cell := raw8 0xF4

private def valueA : Slice := mkSliceFromBits (natToBits 0xA5 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0x5A 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0x3C 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xE1 8)
private def valueF : Slice := mkSliceFromBits (natToBits 0xF2 8)

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def bitsForUnsigned (label : String) (n : Nat) (key : Int) : BitString :=
  match dictKeyBits? key n true with
  | some bits => bits
  | none => panic! s!"{label}: invalid unsigned key {key} for n={n}"

private def mkDictSetSliceBitsRoot! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (bs, value) := entry
      match dictSetSliceWithCells root bs value .set with
      | .ok (some newRoot, _ok, _created, _loaded) => root := newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dict set did not produce a root"
      | .error e =>
          panic! s!"{label}: dict set failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty root table"

private def mkDictSetSliceIntRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Int × Slice))
    (unsigned : Bool := true) : Cell :=
  Id.run do
    let mut pairs : Array (BitString × Slice) := #[]
    for entry in entries do
      let (key, value) := entry
      match dictKeyBits? key n unsigned with
      | some bs => pairs := pairs.push (bs, value)
      | none => panic! s!"{label}: invalid key {key} for n={n}"
    mkDictSetSliceBitsRoot! (label := label) pairs

private def dict4 : Cell :=
  mkDictSetSliceIntRoot! "DICTUSETGET/dict4" 4 #[(0, valueA), (5, valueB), (12, valueC)]

private def dict4Alt : Cell :=
  mkDictSetSliceIntRoot! "DICTUSETGET/dict4-alt" 4 #[(3, valueD), (7, valueE), (14, valueF)]

private def dict1 : Cell :=
  mkDictSetSliceIntRoot! "DICTUSETGET/dict1" 1 #[(0, valueC), (1, valueD)]

private def dict0 : Cell :=
  mkDictSetSliceIntRoot! "DICTUSETGET/dict0" 0 #[((0 : Int), valueA)]

private def expectSetRoot
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (key : Int)
    (value : Slice) : Cell :=
  match dictLookupSetSliceWithCells root (bitsForUnsigned label n key) value .set with
  | .ok (_, some newRoot, _ok, _created, _loaded) => newRoot
  | .ok (_, none, _ok, _created, _loaded) =>
      panic! s!"{label}: expected new root, got none"
  | .error e =>
      panic! s!"{label}: dictLookupSetSliceWithCells failed ({reprStr e})"

private def expectSetCreated
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (key : Int)
    (value : Slice) : Nat :=
  match dictLookupSetSliceWithCells root (bitsForUnsigned label n key) value .set with
  | .ok (_, _newRoot, _ok, created, _loaded) => created
  | .error e =>
      panic! s!"{label}: dictLookupSetSliceWithCells failed ({reprStr e})"

private def expectedHit4_5 : Cell :=
  expectSetRoot "DICTUSETGET/expected/hit/4/5" (some dict4) 4 5 valueF

private def expectedMiss4_4Null : Cell :=
  expectSetRoot "DICTUSETGET/expected/miss/4/4/null" none 4 4 valueA

private def expectedMiss4_4Pair : Cell :=
  expectSetRoot "DICTUSETGET/expected/miss/4/4/pair" (some dict4) 4 4 valueD

private def expectedHit1_0 : Cell :=
  expectSetRoot "DICTUSETGET/expected/hit/1/0" (some dict1) 1 0 valueE

private def expectedMiss1_1 : Cell :=
  expectSetRoot "DICTUSETGET/expected/miss/1/1" (none : Option Cell) 1 1 valueB

private def expectedHit0 : Cell :=
  expectSetRoot "DICTUSETGET/expected/hit/0" (some dict0) 0 0 valueC

private def expectedMiss1023 : Cell :=
  expectSetRoot "DICTUSETGET/expected/miss/1023" none 1023 0 valueD

private def hitCreated4_5 : Nat :=
  expectSetCreated "DICTUSETGET/created/hit/4/5" (some dict4) 4 5 valueF

private def miss4_4NullCreated : Nat :=
  expectSetCreated "DICTUSETGET/created/miss/4/4/null" none 4 4 valueA

private def miss4_4PairCreated : Nat :=
  expectSetCreated "DICTUSETGET/created/miss/4/4/pair" (some dict4) 4 4 valueD

private def hitCreated1_0 : Nat :=
  expectSetCreated "DICTUSETGET/created/hit/1/0" (some dict1) 1 0 valueE

private def miss1_1Created : Nat :=
  expectSetCreated "DICTUSETGET/created/miss/1/1" none 1 1 valueB

private def hit0Created : Nat :=
  expectSetCreated "DICTUSETGET/created/hit/0" (some dict0) 0 0 valueC

private def miss1023Created : Nat :=
  expectSetCreated "DICTUSETGET/created/miss/1023" none 1023 0 valueD

private def exactMinusOne (g : Int) : Int :=
  if g > 0 then g - 1 else 0

private def baseGas : Int := computeExactGasBudget instr
private def exactGasHit4_5 : Int := baseGas + Int.ofNat hitCreated4_5 * cellCreateGasPrice
private def exactGasMiss4_4Null : Int := baseGas + Int.ofNat miss4_4NullCreated * cellCreateGasPrice
private def exactGasMiss4_4Pair : Int := baseGas + Int.ofNat miss4_4PairCreated * cellCreateGasPrice
private def exactGasHit1_0 : Int := baseGas + Int.ofNat hitCreated1_0 * cellCreateGasPrice
private def exactGasMiss1_1 : Int := baseGas + Int.ofNat miss1_1Created * cellCreateGasPrice
private def exactGasHit0 : Int := baseGas + Int.ofNat hit0Created * cellCreateGasPrice
private def exactGasMiss1023 : Int := baseGas + Int.ofNat miss1023Created * cellCreateGasPrice

private def gasHit4_5MinusOne : Int := exactMinusOne exactGasHit4_5
private def gasMiss4_4NullMinusOne : Int := exactMinusOne exactGasMiss4_4Null
private def gasMiss4_4PairMinusOne : Int := exactMinusOne exactGasMiss4_4Pair
private def gasHit1_0MinusOne : Int := exactMinusOne exactGasHit1_0
private def gasMiss1_1MinusOne : Int := exactMinusOne exactGasMiss1_1
private def gasHit0MinusOne : Int := exactMinusOne exactGasHit0
private def gasMiss1023MinusOne : Int := exactMinusOne exactGasMiss1023

private def limitsExactHit4_5 : OracleGasLimits := oracleGasLimitsExact exactGasHit4_5
private def limitsExactMiss4_4Null : OracleGasLimits := oracleGasLimitsExact exactGasMiss4_4Null
private def limitsExactMiss4_4Pair : OracleGasLimits := oracleGasLimitsExact exactGasMiss4_4Pair
private def limitsExactHit1_0 : OracleGasLimits := oracleGasLimitsExact exactGasHit1_0
private def limitsExactMiss1_1 : OracleGasLimits := oracleGasLimitsExact exactGasMiss1_1
private def limitsExactHit0 : OracleGasLimits := oracleGasLimitsExact exactGasHit0
private def limitsExactMiss1023 : OracleGasLimits := oracleGasLimitsExact exactGasMiss1023
private def limitsExactMinusOneHit4_5 : OracleGasLimits := oracleGasLimitsExactMinusOne gasHit4_5MinusOne
private def limitsExactMinusOneMiss4_4Null : OracleGasLimits := oracleGasLimitsExactMinusOne gasMiss4_4NullMinusOne
private def limitsExactMinusOneMiss4_4Pair : OracleGasLimits := oracleGasLimitsExactMinusOne gasMiss4_4PairMinusOne
private def limitsExactMinusOneHit1_0 : OracleGasLimits := oracleGasLimitsExactMinusOne gasHit1_0MinusOne
private def limitsExactMinusOneMiss1_1 : OracleGasLimits := oracleGasLimitsExactMinusOne gasMiss1_1MinusOne
private def limitsExactMinusOneHit0 : OracleGasLimits := oracleGasLimitsExactMinusOne gasHit0MinusOne
private def limitsExactMinusOneMiss1023 : OracleGasLimits := oracleGasLimitsExactMinusOne gasMiss1023MinusOne

private def gasLimitProgram (raw : Cell) (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok p =>
      Cell.mkOrdinary (p.bits ++ raw.bits) (p.refs ++ raw.refs)
  | .error e =>
      panic! s!"DICTUSETGET: gas prefix assembly failed ({reprStr e})"

private def mkStack (newValue : Slice) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[.slice newValue, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some rawF43E
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (rawCode : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some rawCode
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (rawCode : Cell)
    (gas : Int)
    (limits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some (gasLimitProgram rawCode gas)
    initStack := stack
    gasLimits := limits
    fuel := fuel }

private def expectDecode (label : String) (rawCode : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell rawCode) with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed ({e})")
  | .ok (i, bits, rest) =>
      if i != expected || bits != 16 || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected {expected}, got {i} ({bits} bits)")

private def expectDecodeErr (label : String) (rawCode : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell rawCode) with
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} ({bits})")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok _ => throw (IO.userError s!"{label}: expected .invOpcode")
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def expectAssembleOk16 (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")
  | .ok cell =>
      match decodeCp0WithBits (Slice.ofCell cell) with
      | .error e =>
          throw (IO.userError s!"{label}: expected decode success, got {e}")
      | .ok (decoded, bits, rest) =>
          if decoded != i then
            throw (IO.userError s!"{label}: expected {reprStr i}, got {reprStr decoded}")
          else if bits != 16 then
            throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
          else if rest.bitsRemaining + rest.refsRemaining != 0 then
            throw (IO.userError s!"{label}: expected end-of-stream decode")

private def runFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV 909)) stack

private def runDICTUSETGET (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

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
            throw (IO.userError s!"{label}: expected -1 flag, got {flag}")
      | _, _, _ =>
          throw (IO.userError s!"{label}: unexpected stack shape {reprStr st}")

private def genDICTUSETGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 34
  let (tag, rng2) := randNat rng1 0 999_999
  let (baseCase, rng3) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase "fuzz/err/underflow/empty" #[], rng2)
    else if shape = 1 then
      (mkCase "fuzz/err/underflow/one" #[.slice valueA], rng2)
    else if shape = 2 then
      (mkCase "fuzz/err/underflow/two" #[.slice valueA, .int (.num 0)], rng2)
    else if shape = 3 then
      (mkCase "fuzz/err/underflow/three" #[.slice valueA, .int (.num 0), .cell dict4], rng2)
    else if shape = 4 then
      (mkCase "fuzz/ok/hit/4/5" (mkStack valueF 5 (.cell dict4) 4), rng2)
    else if shape = 5 then
      (mkCase "fuzz/ok/miss/4/4-null" (mkStack valueA 4 (.null) 4), rng2)
    else if shape = 6 then
      (mkCase "fuzz/ok/miss/4/4-pair" (mkStack valueD 4 (.cell dict4) 4), rng2)
    else if shape = 7 then
      (mkCase "fuzz/ok/hit/1/0" (mkStack valueE 0 (.cell dict1) 1), rng2)
    else if shape = 8 then
      (mkCase "fuzz/ok/miss/1/1" (mkStack valueB 1 (.null) 1), rng2)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit/0" (mkStack valueC 0 (.cell dict0) 0), rng2)
    else if shape = 10 then
      (mkCase "fuzz/ok/miss/1023" (mkStack valueD 0 (.null) 1023), rng2)
    else if shape = 11 then
      (mkCase "fuzz/err/key/negative" (mkStack valueA (-1) (.cell dict4) 4), rng2)
    else if shape = 12 then
      (mkCase "fuzz/err/key/too-large" (mkStack valueA 16 (.cell dict4) 4), rng2)
    else if shape = 13 then
      (mkCase "fuzz/err/key/nan" #[.slice valueA, .int .nan, .cell dict4, intV 4], rng2)
    else if shape = 14 then
      (mkCase "fuzz/err/key-n0-nonzero" (mkStack valueA 1 (.cell dict0) 0), rng2)
    else if shape = 15 then
      (mkCase "fuzz/err/n-negative" (mkStack valueA 1 (.cell dict4) (-1)), rng2)
    else if shape = 16 then
      (mkCase "fuzz/err/n-too-large" (mkStack valueA 1 (.cell dict4) 1024), rng2)
    else if shape = 17 then
      (mkCase "fuzz/err/n-nan" #[.slice valueA, .int (.num 1), .cell dict4, .int .nan], rng2)
    else if shape = 18 then
      (mkCase "fuzz/err/type-key" #[.slice valueA, .slice valueB, .cell dict4, intV 4], rng2)
    else if shape = 19 then
      (mkCase "fuzz/err/type-value" (#[.int (.num 1), .int (.num 1), .cell dict4, intV 4]), rng2)
    else if shape = 20 then
      (mkCase "fuzz/err/type-dict" (mkStack valueA 1 (.tuple #[]) 4), rng2)
    else if shape = 21 then
      (mkCodeCase "fuzz/ok/alias/f43a" (mkStack valueA 0 (.cell dict4) 4) rawF43A, rng2)
    else if shape = 22 then
      (mkCodeCase "fuzz/ok/alias/f43b" (mkStack valueA 1 (.cell dict4) 4) rawF43B, rng2)
    else if shape = 23 then
      (mkCodeCase "fuzz/ok/alias/f43c" (mkStack valueA 2 (.cell dict4) 4) rawF43C, rng2)
    else if shape = 24 then
      (mkCodeCase "fuzz/ok/alias/f43d" (mkStack valueA 3 (.cell dict4) 4) rawF43D, rng2)
    else if shape = 25 then
      (mkCodeCase "fuzz/ok/alias/f43f" (mkStack valueA 5 (.cell dict4) 4) rawF43F, rng2)
    else if shape = 26 then
      (mkCodeCase "fuzz/err/malformed-root" (mkStack valueA 1 (.cell malformedDictRoot) 4) rawF43E, rng2)
    else if shape = 27 then
      (mkCodeCase "fuzz/err/truncated" (mkStack valueA 1 (.cell dict4) 4) rawF4, rng2)
    else if shape = 28 then
      (mkGasCase "fuzz/gas/exact/hit" (mkStack valueF 5 (.cell dict4) 4) rawF43E exactGasHit4_5 limitsExactHit4_5, rng2)
    else if shape = 29 then
      (mkGasCase "fuzz/gas/exact-minus-one/hit" (mkStack valueF 5 (.cell dict4) 4) rawF43E gasHit4_5MinusOne limitsExactMinusOneHit4_5, rng2)
    else if shape = 30 then
      (mkGasCase "fuzz/gas/exact/miss-null" (mkStack valueA 4 (.null) 4) rawF43E exactGasMiss4_4Null limitsExactMiss4_4Null, rng2)
    else if shape = 31 then
      (mkGasCase "fuzz/gas/exact-minus-one/miss-null" (mkStack valueA 4 (.null) 4) rawF43E gasMiss4_4NullMinusOne limitsExactMinusOneMiss4_4Null, rng2)
    else if shape = 32 then
      (mkGasCase "fuzz/gas/exact/miss-nonempty" (mkStack valueD 4 (.cell dict4) 4) rawF43E exactGasMiss4_4Pair limitsExactMiss4_4Pair, rng2)
    else if shape = 33 then
      (mkGasCase "fuzz/gas/exact-minus-one/miss-nonempty" (mkStack valueD 4 (.cell dict4) 4) rawF43E gasMiss4_4PairMinusOne limitsExactMinusOneMiss4_4Pair, rng2)
    else if shape = 34 then
      (mkCodeCase "fuzz/cross-width/1-hit" (mkStack valueE 0 (.cell dict1) 1) rawF43F, rng2)
    else
      (mkCodeCase (s!"fuzz/noise/{tag}") (mkStack valueC 7 (.cell dict4Alt) 4) rawF43E, rng2)
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        let out := runFallback #[]
        expectOkStack "unit/dispatch/fallback" out #[intV 909] },
    { name := "unit/decoder/f43e"
      run := do
        expectDecode "unit/decoder/f43e" rawF43E (.dictExt (.mutGet true true false .add)) },
    { name := "unit/decoder/f43f"
      run := do
        expectDecode "unit/decoder/f43f" rawF43F (.dictExt (.mutGet true true true .add)) },
    { name := "unit/decoder/f43a"
      run := do
        expectDecode "unit/decoder/f43a" rawF43A (.dictExt (.mutGet false false false .add)) },
    { name := "unit/decoder/f43b"
      run := do
        expectDecode "unit/decoder/f43b" rawF43B (.dictExt (.mutGet false false true .add)) },
    { name := "unit/decoder/f43c"
      run := do
        expectDecode "unit/decoder/f43c" rawF43C (.dictExt (.mutGet true false false .add)) },
    { name := "unit/decoder/f43d"
      run := do
        expectDecode "unit/decoder/f43d" rawF43D (.dictExt (.mutGet true false true .add)) },
    { name := "unit/decoder/boundary"
      run := do
        expectDecodeErr "unit/decoder/f439" rawF439
        expectDecodeErr "unit/decoder/f440" rawF440
        expectDecodeErr "unit/decoder/truncated" rawF4 },
    { name := "unit/asm/encodes"
      run := do
        expectAssembleOk16 "unit/asm/encodes" instr },
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "unit/underflow-empty" (runDICTUSETGET #[]) .stkUnd },
    { name := "unit/runtime/underflow-one"
      run := do
        expectErr "unit/underflow-one" (runDICTUSETGET #[.slice valueA]) .stkUnd },
    { name := "unit/runtime/underflow-two"
      run := do
        expectErr "unit/underflow-two" (runDICTUSETGET #[.slice valueA, .int (.num 1), .cell dict4]) .stkUnd },
    { name := "unit/runtime/underflow-three"
      run := do
        expectErr "unit/underflow-three" (runDICTUSETGET #[.slice valueA, .int (.num 1), .cell dict4]) .stkUnd },
    { name := "unit/runtime/n-range-negative"
      run := do
        expectErr "unit/n-negative" (runDICTUSETGET (mkStack valueA 1 (.cell dict4) (-1))) .rangeChk },
    { name := "unit/runtime/n-range-too-large"
      run := do
        expectErr "unit/n-too-large" (runDICTUSETGET (mkStack valueA 1 (.cell dict4) 1024)) .rangeChk },
    { name := "unit/runtime/key-nan"
      run := do
        expectErr "unit/key-nan" (runDICTUSETGET #[.slice valueA, .int .nan, .cell dict4, intV 4]) .rangeChk }
    ,
    { name := "unit/runtime/type-errors"
      run := do
        expectErr "unit/type-key" (runDICTUSETGET #[.slice valueA, .slice valueA, .cell dict4, intV 4]) .typeChk
        expectErr "unit/type-value" (runDICTUSETGET (#[.int (.num 1), .int (.num 1), .cell dict4, intV 4])) .typeChk
        expectErr "unit/type-dict" (runDICTUSETGET (mkStack valueA 1 (.tuple #[]) 4)) .typeChk },
    { name := "unit/runtime/ok/hit"
      run := do
        expectOkHitShape
          "unit/ok/hit"
          (runDICTUSETGET (mkStack valueF 5 (.cell dict4) 4)) },
    { name := "unit/runtime/ok/miss-null"
      run := do
        expectOkStack
          "unit/ok/miss-null"
          (runDICTUSETGET (mkStack valueA 4 (.null) 4))
          #[.cell expectedMiss4_4Null, intV 0] }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/err/underflow-empty" #[],
    -- [B2]
    mkCase "oracle/err/underflow-one" #[.slice valueA],
    -- [B2]
    mkCase "oracle/err/underflow-two" #[.slice valueA, .int (.num 1), .cell dict4],
    -- [B2]
    mkCase "oracle/err/underflow-three" #[.slice valueA, .int (.num 1), .cell dict4],
    -- [B3][B4]
    mkCase "oracle/err/n-negative" (mkStack valueA 1 (.cell dict4) (-1)),
    -- [B3][B4]
    mkCase "oracle/err/n-too-large" (mkStack valueA 1 (.cell dict4) 1024),
    -- [B3][B4]
    mkCase "oracle/err/n-nan" #[.slice valueA, .int (.num 1), .cell dict4, .int .nan],
    -- [B4]
    mkCase "oracle/err/key/nan" #[.slice valueA, .int .nan, .cell dict4, intV 4],
    -- [B4]
    mkCase "oracle/err/key-negative" (mkStack valueA (-1) (.cell dict4) 4),
    -- [B4]
    mkCase "oracle/err/key-too-large" (mkStack valueA 16 (.cell dict4) 4),
    -- [B4]
    mkCase "oracle/err/key-nonzero-at-n0" (mkStack valueA 1 (.cell dict4) 0),
    -- [B5]
    mkCase "oracle/err/value-type" (#[.int (.num 1), .int (.num 1), .cell dict4, intV 4]),
    -- [B5]
    mkCase "oracle/err/key-type" #[.slice valueA, .slice valueB, .cell dict4, intV 4],
    -- [B5]
    mkCase "oracle/err/dict-type" (mkStack valueA 5 (.tuple #[]) 4),
    -- [B6]
    mkCase "oracle/ok/hit/4/key5" (mkStack valueF 5 (.cell dict4) 4),
    -- [B6]
    mkCase "oracle/ok/hit/4/key12" (mkStack valueD 12 (.cell dict4) 4),
    -- [B6]
    mkCase "oracle/ok/hit/1/key0" (mkStack valueE 0 (.cell dict1) 1),
    -- [B6]
    mkCase "oracle/ok/hit/0/key0" (mkStack valueC 0 (.cell dict0) 0),
    -- [B7]
    mkCase "oracle/ok/miss/4/key4-null" (mkStack valueA 4 (.null) 4),
    -- [B7]
    mkCase "oracle/ok/miss/4/key4-pair" (mkStack valueD 4 (.cell dict4) 4),
    -- [B7]
    mkCase "oracle/ok/miss/1/key1-null" (mkStack valueB 1 (.null) 1),
    -- [B7]
    mkCase "oracle/ok/miss/1023-key0-null" (mkStack valueD 0 (.null) 1023),
    -- [B8]
    mkCase "oracle/err/malformed-root" (mkStack valueA 3 (.cell malformedDictRoot) 4),
    -- [B8]
    mkCodeCase "oracle/ok/alias/f43a" (mkStack valueA 5 (.cell dict4) 4) rawF43A,
    -- [B11]
    mkCodeCase "oracle/err/gap/f439" (mkStack valueA 5 (.cell dict4) 4) rawF439,
    -- [B11]
    mkCodeCase "oracle/err/gap/f440" (mkStack valueA 5 (.cell dict4) 4) rawF440,
    -- [B11]
    mkCodeCase "oracle/err/gap/truncated" (mkStack valueA 5 (.cell dict4) 4) rawF4,
    -- [B10]
    mkCodeCase "oracle/asm/assemble-metadata" (mkStack valueA 5 (.cell dict4) 4) rawF43F,
    -- [B9]
    mkGasCase "oracle/gas/exact-hit" (mkStack valueF 5 (.cell dict4) 4) rawF43E exactGasHit4_5 limitsExactHit4_5,
    -- [B9]
    mkGasCase "oracle/gas/exact-hit-minus-one" (mkStack valueF 5 (.cell dict4) 4) rawF43E gasHit4_5MinusOne limitsExactMinusOneHit4_5,
    -- [B9]
    mkGasCase "oracle/gas/exact-miss-4-null" (mkStack valueA 4 (.null) 4) rawF43E exactGasMiss4_4Null limitsExactMiss4_4Null,
    -- [B9]
    mkGasCase "oracle/gas/exact-miss-4-non-empty" (mkStack valueD 4 (.cell dict4) 4) rawF43E exactGasMiss4_4Pair limitsExactMiss4_4Pair,
    -- [B9]
    mkGasCase "oracle/gas/exact-miss-4-null-minus-one" (mkStack valueA 4 (.null) 4) rawF43E gasMiss4_4NullMinusOne limitsExactMinusOneMiss4_4Null,
    -- [B9]
    mkGasCase "oracle/gas/exact-miss-4-non-empty-minus-one" (mkStack valueD 4 (.cell dict4) 4) rawF43E gasMiss4_4PairMinusOne limitsExactMinusOneMiss4_4Pair,
    -- [B9]
    mkGasCase "oracle/gas/exact-hit1" (mkStack valueE 0 (.cell dict1) 1) rawF43F exactGasHit1_0 limitsExactHit1_0,
    -- [B9]
    mkGasCase "oracle/gas/exact-hit1-minus-one" (mkStack valueE 0 (.cell dict1) 1) rawF43F gasHit1_0MinusOne limitsExactMinusOneHit1_0,
    -- [B9]
    mkGasCase "oracle/gas/exact-miss1" (mkStack valueB 1 (.null) 1) rawF43E exactGasMiss1_1 limitsExactMiss1_1,
    -- [B9]
    mkGasCase "oracle/gas/exact-miss1-minus-one" (mkStack valueB 1 (.null) 1) rawF43E gasMiss1_1MinusOne limitsExactMinusOneMiss1_1,
    -- [B9]
    mkGasCase "oracle/gas/exact-hit0" (mkStack valueC 0 (.cell dict0) 0) rawF43E exactGasHit0 limitsExactHit0,
    -- [B9]
    mkGasCase "oracle/gas/exact-hit0-minus-one" (mkStack valueC 0 (.cell dict0) 0) rawF43E gasHit0MinusOne limitsExactMinusOneHit0,
    -- [B9]
    mkGasCase "oracle/gas/exact-miss1023" (mkStack valueD 0 (.null) 1023) rawF43E exactGasMiss1023 limitsExactMiss1023,
    -- [B9]
    mkGasCase "oracle/gas/exact-miss1023-minus-one" (mkStack valueD 0 (.null) 1023) rawF43E gasMiss1023MinusOne limitsExactMinusOneMiss1023,
    -- [B11][B12]
    mkCodeCase "oracle/alias/f43a" (mkStack valueA 5 (.cell dict4) 4) rawF43A,
    mkCodeCase "oracle/alias/f43b" (mkStack valueA 5 (.cell dict4) 4) rawF43B,
    mkCodeCase "oracle/alias/f43c" (mkStack valueA 5 (.cell dict4) 4) rawF43C,
    mkCodeCase "oracle/alias/f43d" (mkStack valueA 5 (.cell dict4) 4) rawF43D,
    mkCodeCase "oracle/alias/f43f" (mkStack valueA 5 (.cell dict4) 4) rawF43F
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTUSETGETFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUSETGET
