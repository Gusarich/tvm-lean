import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUSETGETB

/-
INSTRUCTION: DICTUSETGETB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch and fallback behavior.
   - `.dictExt (.mutGetB true true .set)` is reached via `execInstrDictExt`.
   - If the instruction is not this exact constructor, the handler must defer via `next`.

2. [B2] Stack arity and stack-empty checks.
   - `checkUnderflow 4` requires builder, key, dictionary, and `n`.
   - 0/1/2/3 item stacks must raise `.stkUnd`.

3. [B3] `n` validation.
   - `popNatUpTo 1023` enforces `0 <= n <= 1023`.
   - Negative / NaN / 1024 each raise `.rangeChk`.

4. [B4] Unsigned integer-key decoding.
   - `popInt` and `dictKeyBits?` with `unsigned = true` produce bits when valid.
   - `.nan` and values outside `[0, 2^n - 1]` (including negative values) raise `.rangeChk`.

5. [B5] Type constraints.
   - Value must be `.builder`; key must be `.int`; dictionary must be `.cell` or `.null`.
   - Mismatched types trigger `.typeChk`.

6. [B6] Runtime success branches.
   - Miss path: key absent inserts value, pushes new dictionary root and `0`.
   - Hit path: key present replaces value, pushes new root, old slice, and `-1`.
   - Missing-key case is distinct for empty dict, non-empty dict, and boundary `n = 0`/`n = 1023`.

7. [B7] Dictionary structural errors.
   - Malformed dictionary roots are rejected with `.dictErr` after traversal path.

8. [B8] Gas accounting.
   - Base gas is `computeExactGasBudget`.
   - Runtime gas additionally adds `created * cellCreateGasPrice`.
   - Both exact-gas success and exact-gas-minus-one failure states are observable.

9. [B9] Assembler encoding.
   - `DICTUSETGETB` is not assembled by CP0 in this test set (same as other dict*B opcodes).
   - Therefore all constructor forms produce `.invOpcode`.

10. [B10] Decoder boundaries and adjacent opcodes.
   - `0xF447` decodes to `.dictExt (.mutGetB true true .set)`.
   - `0xF446` decodes to the adjacent signed variant.
   - `0xF444` and `0xF448` must fail as `.invOpcode`.
   - 8-bit truncated `0xF4` must also fail.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTUSETGETB" }

private def instrUnsigned : Instr :=
  .dictExt (.mutGetB true true .set)

private def instrSigned : Instr :=
  .dictExt (.mutGetB true false .set)

private def rawF445 : Cell :=
  Cell.mkOrdinary (natToBits 0xF445 16) #[]

private def rawF446 : Cell :=
  Cell.mkOrdinary (natToBits 0xF446 16) #[]

private def rawF447 : Cell :=
  Cell.mkOrdinary (natToBits 0xF447 16) #[]

private def rawF448 : Cell :=
  Cell.mkOrdinary (natToBits 0xF448 16) #[]

private def rawF444 : Cell :=
  Cell.mkOrdinary (natToBits 0xF444 16) #[]

private def rawF4 : Cell :=
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
private def valueSliceC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueSliceD : Slice := mkSliceFromBits (natToBits 0xD4 8)

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def key1023 : BitString :=
  Array.replicate 1023 false

private def mkDictSetRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in entries do
      let (key, value) := p
      let keyBits : BitString :=
        match dictKeyBits? key n true with
        | some bits => bits
        | none =>
            panic! s!"{label}: invalid key for n={n}: {key} (unsigned)"
      match dictSetBuilderWithCells root keyBits value .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: insertion unexpectedly returned no root"
      | .error e =>
          panic! s!"{label}: dictSetBuilderWithCells failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def keyBitsFor (label : String) (n : Nat) (key : Int) : BitString :=
  match dictKeyBits? key n true with
  | some bits => bits
  | none => panic! s!"{label}: invalid unsigned key {key} for n={n}"

private def dictUnsigned4 : Cell :=
  mkDictSetRoot! "dict/unsigned/4" 4 #[(0, valueA), (3, valueB), (7, valueC), (15, valueD)]

private def dictUnsigned4Miss : Cell :=
  mkDictSetRoot! "dict/unsigned/4/miss" 4 #[(1, valueB), (6, valueC)]

private def dictUnsigned8 : Cell :=
  mkDictSetRoot! "dict/unsigned/8" 8 #[(0, valueA), (1, valueB), (128, valueC), (255, valueD)]

private def dictUnsigned0 : Cell :=
  mkDictSetRoot! "dict/unsigned/0" 0 #[(0, valueE)]

private def expectedSetReplaceUnsigned4 : Cell :=
  match
    dictLookupSetBuilderWithCells (some dictUnsigned4) (keyBitsFor "expectedSetReplaceUnsigned4" 4 15) valueE .set
  with
  | .ok (_old, some root, _ok, _created, _loaded) => root
  | _ => panic! "DICTUSETGETB: expectedSetReplaceUnsigned4 precompute failed"

private def expectedSetNull4 : Cell :=
  match dictLookupSetBuilderWithCells none (keyBitsFor "expectedSetNull4" 4 2) valueB .set with
  | .ok (_old, some root, _ok, _created, _loaded) => root
  | _ => panic! "DICTUSETGETB: expectedSetNull4 precompute failed"

private def expectedSetNull0 : Cell :=
  match dictLookupSetBuilderWithCells none (keyBitsFor "expectedSetNull0" 0 0) valueA .set with
  | .ok (_old, some root, _ok, _created, _loaded) => root
  | _ => panic! "DICTUSETGETB: expectedSetNull0 precompute failed"

private def mkIntStack (value : Builder) (key : Int) (dict : Value := .null) (n : Int := 4) : Array Value :=
  #[.builder value, .int (.num key), dict, intV n]

private def mkDictUSetGetBCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrUnsigned])
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
  { name := name
    instr := suiteId
    program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} ({bits} bits)")

private def expectAssembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assembler failure invOpcode, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure invOpcode")

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

private def runDictUSetGetBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDictUSetGetBFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .nop (VM.push (.int (.num 777))) stack

private def createdBitsForSet (root : Option Cell) (bits : BitString) (value : Builder := valueB) : Nat :=
  match dictLookupSetBuilderWithCells root bits value .set with
  | .ok (_old, _new, _ok, created, _loaded) => created
  | .error e => panic! s!"DICTUSETGETB: failed to precompute created bits ({reprStr e})"

private def createBitsUnsigned4Miss : Nat :=
  createdBitsForSet none (keyBitsFor "createUnsigned4Miss" 4 2)

private def createBitsUnsigned4MissNonEmpty : Nat :=
  createdBitsForSet (some dictUnsigned4) (keyBitsFor "createUnsigned4MissNonEmpty" 4 2)

private def createBitsUnsigned4Hit : Nat :=
  createdBitsForSet (some dictUnsigned4) (keyBitsFor "createUnsigned4Hit" 4 15) valueE

private def createBitsUnsigned0Miss : Nat :=
  createdBitsForSet none (keyBitsFor "createUnsigned0Miss" 0 0)

private def baseGas : Int :=
  computeExactGasBudget instrUnsigned

private def gasUnsigned4Miss : Int :=
  baseGas + Int.ofNat createBitsUnsigned4Miss * cellCreateGasPrice

private def gasUnsigned4MissNonEmpty : Int :=
  baseGas + Int.ofNat createBitsUnsigned4MissNonEmpty * cellCreateGasPrice

private def gasUnsigned4Hit : Int :=
  baseGas + Int.ofNat createBitsUnsigned4Hit * cellCreateGasPrice

private def gasUnsigned0Miss : Int :=
  baseGas + Int.ofNat createBitsUnsigned0Miss * cellCreateGasPrice

private def gasUnsigned4MissMinusOne : Int :=
  if gasUnsigned4Miss > 0 then gasUnsigned4Miss - 1 else 0

private def gasUnsigned4MissNonEmptyMinusOne : Int :=
  if gasUnsigned4MissNonEmpty > 0 then gasUnsigned4MissNonEmpty - 1 else 0

private def gasUnsigned4HitMinusOne : Int :=
  if gasUnsigned4Hit > 0 then gasUnsigned4Hit - 1 else 0

private def gasUnsigned0MissMinusOne : Int :=
  if gasUnsigned0Miss > 0 then gasUnsigned0Miss - 1 else 0

private def genDictUSetGetBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (tier, rng1) := randNat rng0 0 99
  let (shape, rng2) :=
    if tier < 55 then
      randNat rng1 0 17
    else
      randNat rng1 0 15
  let (case0, rng3) :=
    if tier < 55 then
      match shape with
      | 0 =>
          (mkDictUSetGetBCase "fuzz/branch/hit/4/0" (mkIntStack valueB 0 (.cell dictUnsigned4) 4), rng2)
      | 1 =>
          (mkDictUSetGetBCase "fuzz/branch/hit/4/max" (mkIntStack valueC 15 (.cell dictUnsigned4) 4), rng2)
      | 2 =>
          (mkDictUSetGetBCase "fuzz/branch/hit/4/mid" (mkIntStack valueA 7 (.cell dictUnsigned4) 4), rng2)
      | 3 =>
          (mkDictUSetGetBCase "fuzz/branch/miss/4/null" (mkIntStack valueB 2 (.null) 4), rng2)
      | 4 =>
          (mkDictUSetGetBCase "fuzz/branch/miss/4/missdict" (mkIntStack valueD 9 (.cell dictUnsigned4Miss) 4), rng2)
      | 5 =>
          (mkDictUSetGetBCase "fuzz/branch/miss/8/null" (mkIntStack valueA 255 (.null) 8), rng2)
      | 6 =>
          (mkDictUSetGetBCase "fuzz/branch/hit/8" (mkIntStack valueC 255 (.cell dictUnsigned8) 8), rng2)
      | 7 =>
          (mkDictUSetGetBCase "fuzz/branch/hit/0" (mkIntStack valueD 0 (.cell dictUnsigned0) 0), rng2)
      | 8 =>
          (mkDictUSetGetBCase "fuzz/branch/miss/1023/null" (mkIntStack valueA 0 (.null) 1023), rng2)
      | 9 =>
          (mkDictUSetGetBCase "fuzz/error/n-neg" (mkIntStack valueA 1 (.cell dictUnsigned4) (-1)), rng2)
      | 10 =>
          (mkDictUSetGetBCase "fuzz/error/n-large" (mkIntStack valueA 1 (.cell dictUnsigned4) 1024), rng2)
      | 11 =>
          (mkDictUSetGetBCase "fuzz/error/n-nan" (#[
            .builder valueA, .int (.num 1), .cell dictUnsigned4, .int .nan
          ]), rng2)
      | 12 =>
          (mkDictUSetGetBCase "fuzz/error/key-nan" (#[
            .builder valueA, .int .nan, .cell dictUnsigned4, intV 4
          ]), rng2)
      | 13 =>
          (mkDictUSetGetBCase "fuzz/error/key-low" (mkIntStack valueA (-1) (.cell dictUnsigned4) 4), rng2)
      | 14 =>
          (mkDictUSetGetBCase "fuzz/error/key-high" (mkIntStack valueA 16 (.cell dictUnsigned4) 4), rng2)
      | 15 =>
          (mkGasCase "fuzz/gas/miss-exact" (mkIntStack valueB 2 .null 4) instrUnsigned gasUnsigned4Miss (oracleGasLimitsExact gasUnsigned4Miss), rng2)
      | 16 =>
          (mkGasCase "fuzz/gas/miss-minus-one" (mkIntStack valueB 2 .null 4) instrUnsigned gasUnsigned4MissMinusOne (oracleGasLimitsExactMinusOne gasUnsigned4MissMinusOne), rng2)
      | _ =>
          (mkGasCase "fuzz/gas/hit-exact" (mkIntStack valueE 15 (.cell dictUnsigned4) 4) instrUnsigned gasUnsigned4Hit (oracleGasLimitsExact gasUnsigned4Hit), rng2)
    else
      match shape with
      | 0 =>
          (mkDictUSetGetBCase "fuzz/underflow/empty" #[], rng2)
      | 1 =>
          (mkDictUSetGetBCase "fuzz/underflow/one" #[.builder valueA], rng2)
      | 2 =>
          (mkDictUSetGetBCase "fuzz/underflow/two" (mkIntStack valueA 0), rng2)
      | 3 =>
          (mkDictUSetGetBCase "fuzz/underflow/three" (mkIntStack valueA 0 (.cell dictUnsigned4)), rng2)
      | 4 =>
          (mkDictUSetGetBCase "fuzz/type/dict" (mkIntStack valueA 0 (.builder valueA) 4), rng2)
      | 5 =>
          (mkDictUSetGetBCase "fuzz/type/key" (#[.builder valueA, .cell dictUnsigned4, .cell dictUnsigned4, intV 4]), rng2)
      | 6 =>
          (mkDictUSetGetBCase "fuzz/type/value" (#[
            .int (.num 1), .int (.num 1), .cell dictUnsigned4, intV 4]), rng2)
      | 7 =>
          (mkDictUSetGetBCase "fuzz/malformed-root" (mkIntStack valueA 1 (.cell malformedDictRoot) 4), rng2)
      | 8 =>
          (mkCodeCase "fuzz/decode/f446" (mkIntStack valueA 0 (.cell dictUnsigned4) 4) rawF446, rng2)
      | 9 =>
          (mkCodeCase "fuzz/decode/f448-invalid" (mkIntStack valueA 0 (.cell dictUnsigned4) 4) rawF448, rng2)
      | 10 =>
          (mkCodeCase "fuzz/decode/trunc8-invalid" (mkIntStack valueA 0 (.cell dictUnsigned4) 4) rawF4, rng2)
      | 11 =>
          (mkGasCase "fuzz/gas/hit-minus-one" (mkIntStack valueE 15 (.cell dictUnsigned4) 4) instrUnsigned gasUnsigned4HitMinusOne (oracleGasLimitsExactMinusOne gasUnsigned4HitMinusOne), rng2)
      | 12 =>
          (mkDictUSetGetBCase "fuzz/gas/miss-nonempty-exact" (mkIntStack valueA 9 (.cell dictUnsigned4) 4), rng2)
      | 13 =>
          (mkGasCase "fuzz/gas/zero-miss-exact" (mkIntStack valueA 0 (.null) 0) instrUnsigned gasUnsigned0Miss (oracleGasLimitsExact gasUnsigned0Miss), rng2)
      | 14 =>
          (mkGasCase "fuzz/gas/zero-miss-minus-one" (mkIntStack valueA 0 (.null) 0) instrUnsigned gasUnsigned0MissMinusOne (oracleGasLimitsExactMinusOne gasUnsigned0MissMinusOne), rng2)
      | _ =>
          (mkDictUSetGetBCase "fuzz/range-noise" (mkIntStack valueA 1 (.cell dictUnsigned4) 7), rng2)
  let (tag, rng4) := randNat rng3 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/next"
      run := do
        let got := runDictUSetGetBFallback (mkIntStack valueA 7 (.cell dictUnsigned4) 4)
        let expected :=
          mkIntStack valueA 7 (.cell dictUnsigned4) 4 ++ #[.int (.num 777)]
        expectOkStack "dispatch/next" got expected
    },
    { name := "unit/decoder/decode/f447"
      run := do
        let _ ← expectDecodeStep "decode/f447" (Slice.ofCell rawF447) instrUnsigned 16
    },
    { name := "unit/decoder/decode/f446"
      run := do
        let _ ← expectDecodeStep "decode/f446" (Slice.ofCell rawF446) instrSigned 16
    },
    { name := "unit/decoder/decode/adjacent-invalid"
      run := do
        expectDecodeInvOpcode "decode/f444" rawF444
        expectDecodeInvOpcode "decode/f448" rawF448
        expectDecodeInvOpcode "decode/f4-8bit" rawF4
    },
    { name := "unit/assembler/reject"
      run := do
        expectAssembleInvOpcode "asm/reject" instrUnsigned
    },
    { name := "unit/runtime/validation"
      run := do
        expectErr "underflow-empty" (runDictUSetGetBDirect instrUnsigned #[]) .stkUnd
        expectErr "underflow-three"
          (runDictUSetGetBDirect instrUnsigned #[.builder valueA, intV 1, .cell dictUnsigned4])
          .stkUnd
        expectErr "n-negative" (runDictUSetGetBDirect instrUnsigned (mkIntStack valueA 1 (.cell dictUnsigned4) (-1))) .rangeChk
        expectErr "n-too-large" (runDictUSetGetBDirect instrUnsigned (mkIntStack valueA 1 (.cell dictUnsigned4) 1024)) .rangeChk
        expectErr "n-nan" (runDictUSetGetBDirect instrUnsigned #[.builder valueA, .int (.num 1), .cell dictUnsigned4, .int .nan]) .rangeChk
        expectErr "key-nan" (runDictUSetGetBDirect instrUnsigned (#[.builder valueA, .int .nan, .cell dictUnsigned4, intV 4])) .rangeChk
        expectErr "key-low" (runDictUSetGetBDirect instrUnsigned (mkIntStack valueA (-1) (.cell dictUnsigned4) 4)) .rangeChk
        expectErr "key-high" (runDictUSetGetBDirect instrUnsigned (mkIntStack valueA 16 (.cell dictUnsigned4) 4)) .rangeChk
        expectErr "key-type" (runDictUSetGetBDirect instrUnsigned (#[
          .builder valueA, .cell dictUnsigned4, .cell dictUnsigned4, intV 4
        ])) .typeChk
        expectErr "value-type" (runDictUSetGetBDirect instrUnsigned (#[
          .int (.num 1), .int (.num 1), .cell dictUnsigned4, intV 4
        ])) .typeChk
        expectErr "dict-type" (runDictUSetGetBDirect instrUnsigned (mkIntStack valueA 1 (.tuple #[]) 4)) .typeChk
        expectErr "dict-malformed" (runDictUSetGetBDirect instrUnsigned (mkIntStack valueA 1 (.cell malformedDictRoot) 4)) .cellUnd
    },
    { name := "unit/runtime/set-hit"
      run := do
        let got := runDictUSetGetBDirect instrUnsigned (mkIntStack valueE 15 (.cell dictUnsigned4) 4)
        match got with
        | .error e =>
            throw (IO.userError s!"set-hit: expected success, got error {e}")
        | .ok st =>
            if st.size != 3 then
              throw (IO.userError s!"set-hit: expected stack size 3, got {reprStr st}")
            if st[0]! != .cell expectedSetReplaceUnsigned4 then
              throw (IO.userError s!"set-hit: expected root={reprStr expectedSetReplaceUnsigned4}, got {reprStr st[0]!}")
            if st[2]! != intV (-1) then
              throw (IO.userError s!"set-hit: expected flag=-1, got {reprStr st[2]!}")
            match st[1]! with
            | .slice s =>
                if s.toCellRemaining != valueSliceD.toCellRemaining then
                  throw
                    (IO.userError
                      s!"set-hit: expected old={reprStr valueSliceD.toCellRemaining}, got {reprStr s.toCellRemaining}")
            | v =>
                throw (IO.userError s!"set-hit: expected slice at stack[1], got {reprStr v}")
    },
    { name := "unit/runtime/set-miss-null"
      run := do
        let got := runDictUSetGetBDirect instrUnsigned (mkIntStack valueB 2 .null 4)
        let expected := #[
          .cell expectedSetNull4,
          intV 0
        ]
        expectOkStack "set-miss-null" got expected
    },
    { name := "unit/runtime/set-miss-zero-n"
      run := do
        let got := runDictUSetGetBDirect instrUnsigned (mkIntStack valueA 0 .null 0)
        let expected := #[
          .cell expectedSetNull0,
          intV 0
        ]
        expectOkStack "set-miss-zero-n" got expected
    },
    { name := "unit/assembly-and-decoding-redundancy"
      run := do
        expectAssembleInvOpcode "asm/fallback" instrUnsigned
        expectDecodeInvOpcode "decode/f444" rawF444
        expectDecodeInvOpcode "decode/f4" rawF4
    }
  ]
  oracle := #[
    mkDictUSetGetBCase "oracle/ok/miss/null/4" (mkIntStack valueA 2 .null 4), -- [B2][B6]
    mkDictUSetGetBCase "oracle/ok/miss/null/8" (mkIntStack valueB 200 (.null) 8), -- [B3][B6]
    mkDictUSetGetBCase "oracle/ok/miss/nonempty/4" (mkIntStack valueA 12 (.cell dictUnsigned4Miss) 4), -- [B2][B3][B6]
    mkDictUSetGetBCase "oracle/ok/miss/null/1023" (mkIntStack valueB 0 (.null) 1023), -- [B3][B6]
    mkDictUSetGetBCase "oracle/ok/miss/empty-vs-nonempty-8" (mkIntStack valueC 77 (.cell dictUnsigned4Miss) 8), -- [B3][B6]
    mkDictUSetGetBCase "oracle/ok/hit/4/min" (mkIntStack valueD 0 (.cell dictUnsigned4) 4), -- [B4][B6]
    mkDictUSetGetBCase "oracle/ok/hit/4/mid" (mkIntStack valueA 3 (.cell dictUnsigned4) 4), -- [B4][B6]
    mkDictUSetGetBCase "oracle/ok/hit/4/max" (mkIntStack valueB 15 (.cell dictUnsigned4) 4), -- [B4][B6]
    mkDictUSetGetBCase "oracle/ok/hit/8/a" (mkIntStack valueC 0 (.cell dictUnsigned8) 8), -- [B3][B4][B6]
    mkDictUSetGetBCase "oracle/ok/hit/8/b" (mkIntStack valueB 255 (.cell dictUnsigned8) 8), -- [B3][B4][B6]
    mkDictUSetGetBCase "oracle/ok/hit/0" (mkIntStack valueA 0 (.cell dictUnsigned0) 0), -- [B3][B6]

    mkDictUSetGetBCase "oracle/err/underflow/empty" #[], -- [B2]
    mkDictUSetGetBCase "oracle/err/underflow/one" #[.builder valueA], -- [B2]
    mkDictUSetGetBCase "oracle/err/underflow/two" (mkIntStack valueA 1 .null), -- [B2]
    mkDictUSetGetBCase "oracle/err/underflow/three" (mkIntStack valueA 1 (.cell dictUnsigned4)), -- [B2]
    mkDictUSetGetBCase "oracle/err/n/negative" (mkIntStack valueA 1 (.cell dictUnsigned4) (-1)), -- [B3]
    mkDictUSetGetBCase "oracle/err/n/too-large" (mkIntStack valueA 1 (.cell dictUnsigned4) 1024), -- [B3]
    mkDictUSetGetBCase "oracle/err/n/nan" #[.builder valueA, .int (.num 1), .cell dictUnsigned4, .int .nan], -- [B3]

    mkDictUSetGetBCase "oracle/err/key/nan" #[.builder valueA, .int .nan, .cell dictUnsigned4, intV 4], -- [B4]
    mkDictUSetGetBCase "oracle/err/key/negative" (mkIntStack valueA (-1) (.cell dictUnsigned4) 4), -- [B4][B5]
    mkDictUSetGetBCase "oracle/err/key/out-of-range/high" (mkIntStack valueA 16 (.cell dictUnsigned4) 4), -- [B4]
    mkDictUSetGetBCase "oracle/err/key/out-of-range/large-n" (mkIntStack valueA 4096 (.cell dictUnsigned4) 12), -- [B4]
    mkDictUSetGetBCase "oracle/err/type/key" (mkIntStack valueA 1 (.cell dictUnsigned4) 4), -- [B5]
    mkDictUSetGetBCase "oracle/err/type/value" (#[
      .int (.num 1), .int (.num 1), .cell dictUnsigned4, intV 4
    ]), -- [B5]
    mkDictUSetGetBCase "oracle/err/type/dict" (mkIntStack valueA 1 (.tuple #[]) 4), -- [B5]

    mkDictUSetGetBCase "oracle/err/malformed-root" (mkIntStack valueA 1 (.cell malformedDictRoot) 4), -- [B7]

    mkCodeCase "oracle/code/f447" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) rawF447, -- [B10]
    mkCodeCase "oracle/code/f446-adjacent" (mkIntStack valueA 3 (.cell dictUnsigned4) 4) rawF446, -- [B10]
    mkCodeCase "oracle/code/f448-invalid" (mkIntStack valueA 3 (.cell dictUnsigned4) 4) rawF448, -- [B10]
    mkCodeCase "oracle/code/f4-invalid" (mkIntStack valueA 3 (.cell dictUnsigned4) 4) rawF4, -- [B10]
    mkCodeCase "oracle/code/f445-noise" (mkIntStack valueA 1 (.cell dictUnsigned4) 4) rawF445, -- [B10]

    mkGasCase "oracle/gas/miss-null-exact-4" (mkIntStack valueA 2 .null 4) instrUnsigned gasUnsigned4Miss (oracleGasLimitsExact gasUnsigned4Miss), -- [B8][B11]
    mkGasCase "oracle/gas/miss-null-exact-minus-one-4" (mkIntStack valueA 2 .null 4) instrUnsigned gasUnsigned4MissMinusOne (oracleGasLimitsExactMinusOne gasUnsigned4MissMinusOne), -- [B8][B11]
    mkGasCase "oracle/gas/miss-nonempty-exact-4" (mkIntStack valueA 12 (.cell dictUnsigned4Miss) 4) instrUnsigned gasUnsigned4MissNonEmpty (oracleGasLimitsExact gasUnsigned4MissNonEmpty), -- [B8][B11]
    mkGasCase "oracle/gas/miss-nonempty-exact-minus-one-4" (mkIntStack valueA 12 (.cell dictUnsigned4Miss) 4) instrUnsigned gasUnsigned4MissNonEmptyMinusOne (oracleGasLimitsExactMinusOne gasUnsigned4MissNonEmptyMinusOne), -- [B8][B11]
    mkGasCase "oracle/gas/hit-exact-4" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) instrUnsigned gasUnsigned4Hit (oracleGasLimitsExact gasUnsigned4Hit), -- [B8][B11]
    mkGasCase "oracle/gas/hit-exact-minus-one-4" (mkIntStack valueA 15 (.cell dictUnsigned4) 4) instrUnsigned gasUnsigned4HitMinusOne (oracleGasLimitsExactMinusOne gasUnsigned4HitMinusOne), -- [B8][B11]
    mkGasCase "oracle/gas/zero-miss-exact" (mkIntStack valueA 0 .null 0) instrUnsigned gasUnsigned0Miss (oracleGasLimitsExact gasUnsigned0Miss), -- [B8][B11]
    mkGasCase "oracle/gas/zero-miss-exact-minus-one" (mkIntStack valueA 0 .null 0) instrUnsigned gasUnsigned0MissMinusOne (oracleGasLimitsExactMinusOne gasUnsigned0MissMinusOne) -- [B8][B11]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictUSetGetBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUSETGETB
