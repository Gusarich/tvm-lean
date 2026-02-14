import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREPLACEREF

/-!
INSTRUCTION: DICTREPLACEREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch.
   - `.dictSet` is handled by `execInstrDictDictSet`; non-matching instructions must continue to
     `next` untouched.

2. [B2] Runtime preamble.
   - `checkUnderflow 4` is mandatory.
   - stack pops are in order `n`, `dict`, `key`, `valueRef`.
   - `popMaybeCell`, `popSlice`, `popCell` are type-checked before mutation.

3. [B3] Width validation.
   - `popNatUpTo 1023` rejects negative values, `NaN`, and out-of-range widths (`n > 1023`).

4. [B4] Non-int key materialization.
   - Non-int key path uses `popSlice` and `prefetch_bits n`.
   - If the slice has fewer than `n` bits, `cellUnd` is raised.
   - `n = 0` accepts any key slice and uses empty key bits.

5. [B5] Replace semantics vs miss.
   - `mode = .replace` never throws on miss.
   - Miss path: dictionary unchanged, stack receives `oldRoot`/`null` plus `0`.
   - Hit path: dictionary updated, stack receives `newRoot` plus `-1`.

6. [B6] By-ref value path.
   - By-ref mode requires a `.cell`; non-cell value raises `typeChk`.

7. [B7] Malformed dictionary structural errors.
   - `dictSetRefWithCells` can raise `.dictErr`/`.cellUnd` through label parsing/validation.

8. [B8] Assembler encoding.
   - Valid encoding is `.dictSet false false true .replace` (`0xF423`).
   - Unsigned flag is invalid for non-int variants (`.dictSet false true ... .replace`) and is rejected
     by `assembleCp0` with `.invOpcode`.

9. [B9] Decoder behavior.
   - Exact decode for `0xF423` and boundary opcodes `0xF422`/`0xF424`/`0xF425`/`0xF426`/`0xF427`
     must map to the intended `dictSet` variants.
   - Truncated 8-bit input must fail with `invOpcode`.

10. [B10] Gas accounting.
   - Base budget is `computeExactGasBudget instr`.
   - Miss path has no `created`-cell penalty.
   - Hit path adds `cellCreateGasPrice * created`.
   - `exact` budget must pass, `exact-1` must fail for both miss and hit branches.

11. [B11] Boundary key widths.
   - `n = 0` is a meaningful boundary with empty key matching behavior.
   - `n = 1023` is the maximum accepted width in runtime checks.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTREPLACEREF" }

private def instr : Instr :=
  .dictSet false false true .replace

private def dispatchSentinel : Int :=
  13021

private def dictNull : Value :=
  .null

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC 8) #[]

private def valueD : Cell :=
  Cell.mkOrdinary (natToBits 0xD 8) #[]

private def valueSliceA : Slice :=
  mkSliceWithBitsRefs (natToBits 0xAA 8)

private def valueSliceB : Slice :=
  mkSliceWithBitsRefs (natToBits 0x55 8)

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b00 2) #[]

private def k0 : BitString := #[]
private def k1 : BitString := natToBits 0b0 1
private def k4A : BitString := natToBits 0b0010 4
private def k4B : BitString := natToBits 0b0011 4
private def k8A : BitString := natToBits 0x55 8
private def k8B : BitString := natToBits 0xAA 8
private def k8C : BitString := natToBits 0xA5 8
private def k8D : BitString := natToBits 0xA9 8
private def k16A : BitString := natToBits 0xBEEF 16
private def k1023 : BitString := fullBuilder1023.bits

private def s0 : Slice := mkSliceWithBitsRefs k0
private def s1 : Slice := mkSliceWithBitsRefs k1
private def s4A : Slice := mkSliceWithBitsRefs k4A
private def s4B : Slice := mkSliceWithBitsRefs k4B
private def s8A : Slice := mkSliceWithBitsRefs k8A
private def s8B : Slice := mkSliceWithBitsRefs k8B
private def s8C : Slice := mkSliceWithBitsRefs k8C
private def s8D : Slice := mkSliceWithBitsRefs k8D
private def s16A : Slice := mkSliceWithBitsRefs k16A
private def s1023 : Slice := mkSliceWithBitsRefs k1023
private def sShortA : Slice := mkSliceWithBitsRefs (natToBits 0b101 3)
private def sExtraA : Slice := mkSliceWithBitsRefs (natToBits 0xAB 9)
private def sKeyOnly : Slice := mkSliceWithBitsRefs (natToBits 0x55 8)

private def rawOpcodeF422 : Cell :=
  Cell.mkOrdinary (natToBits 0xF422 16) #[]

private def rawOpcodeF423 : Cell :=
  Cell.mkOrdinary (natToBits 0xF423 16) #[]

private def rawOpcodeF424 : Cell :=
  Cell.mkOrdinary (natToBits 0xF424 16) #[]

private def rawOpcodeF425 : Cell :=
  Cell.mkOrdinary (natToBits 0xF425 16) #[]

private def rawOpcodeF426 : Cell :=
  Cell.mkOrdinary (natToBits 0xF426 16) #[]

private def rawOpcodeF427 : Cell :=
  Cell.mkOrdinary (natToBits 0xF427 16) #[]

private def rawOpcodeF4 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def mkDictSetRefRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetRefWithCells root k v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root during construction"
      | .error e =>
          panic! s!"{label}: dict set failed for {reprStr k} with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty root"

private def dictSingle8 : Cell :=
  mkDictSetRefRoot! "dictSingle8" #[(k8A, valueA)]

private def dictPair8 : Cell :=
  mkDictSetRefRoot! "dictPair8" #[(k8A, valueA), (k8B, valueB)]

private def dictFork8 : Cell :=
  mkDictSetRefRoot! "dictFork8" #[(k8C, valueC), (k8D, valueD)]

private def dictSingle4 : Cell :=
  mkDictSetRefRoot! "dictSingle4" #[(k4A, valueA)]

private def dictShared4 : Cell :=
  mkDictSetRefRoot! "dictShared4" #[(k4A, valueA), (k4B, valueB)]

private def dictSingle0 : Cell :=
  mkDictSetRefRoot! "dictSingle0" #[(k0, valueC)]

private def dictSingle16 : Cell :=
  mkDictSetRefRoot! "dictSingle16" #[(k16A, valueD)]

private def single8ReplaceCreated : Nat :=
  match dictSetRefWithCells (some dictSingle8) k8A valueB .replace with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error _ => 0

private def pair8ReplaceCreated : Nat :=
  match dictSetRefWithCells (some dictPair8) k8A valueB .replace with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error _ => 0

private def shared4ReplaceCreated : Nat :=
  match dictSetRefWithCells (some dictShared4) k4A valueB .replace with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error _ => 0

private def single0ReplaceCreated : Nat :=
  match dictSetRefWithCells (some dictSingle0) k0 valueA .replace with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error _ => 0

private def baseGas : Int :=
  computeExactGasBudget instr

private def baseGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def hitSingle8Gas : Int :=
  baseGas + Int.ofNat single8ReplaceCreated * cellCreateGasPrice

private def hitSingle8GasMinusOne : Int :=
  if hitSingle8Gas > 0 then hitSingle8Gas - 1 else 0

private def hitPair8Gas : Int :=
  baseGas + Int.ofNat pair8ReplaceCreated * cellCreateGasPrice

private def hitPair8GasMinusOne : Int :=
  if hitPair8Gas > 0 then hitPair8Gas - 1 else 0

private def hitShared4Gas : Int :=
  baseGas + Int.ofNat shared4ReplaceCreated * cellCreateGasPrice

private def hitShared4GasMinusOne : Int :=
  if hitShared4Gas > 0 then hitShared4Gas - 1 else 0

private def hitZeroGas : Int :=
  baseGas + Int.ofNat single0ReplaceCreated * cellCreateGasPrice

private def hitZeroGasMinusOne : Int :=
  if hitZeroGas > 0 then hitZeroGas - 1 else 0

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instr])
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
    (stack : Array Value := #[])
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDICTREPLACEREFFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def genDICTREPLACEREFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/hit/single8" (#[
        .cell valueA,
        .slice s8A,
        .cell dictSingle8,
        intV 8,
      ]), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/hit/pair8" (#[
        .cell valueB,
        .slice s8A,
        .cell dictPair8,
        intV 8,
      ]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/hit/fork8" (#[
        .cell valueA,
        .slice s8C,
        .cell dictFork8,
        intV 8,
      ]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/hit/shared4" (#[
        .cell valueC,
        .slice s4A,
        .cell dictShared4,
        intV 4,
      ]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/hit/zero-width" (#[
        .cell valueD,
        .slice s8A,
        .cell dictSingle0,
        intV 0,
      ]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/miss/null" (#[
        .cell valueA,
        .slice s8D,
        dictNull,
        intV 8,
      ]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/miss/non-empty" (#[
        .cell valueA,
        .slice s8D,
        .cell dictSingle8,
        intV 8,
      ]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/miss/zero-width" (#[
        .cell valueB,
        .slice sKeyOnly,
        .cell dictSingle0,
        intV 0,
      ]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/extra-key-bits" (#[
        .cell valueC,
        .slice sExtraA,
        .cell dictSingle8,
        intV 8,
      ]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit/max-width" (#[
        .cell valueB,
        .slice s1023,
        dictNull,
        intV 1023,
      ]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/underflow/empty" #[], rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/underflow/one" #[intV 8], rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/underflow/two" #[intV 8, dictNull], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/underflow/three" #[intV 8, .cell dictPair8, .slice s8A], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/n/negative" (#[
        .cell valueB,
        .slice s8A,
        .cell dictPair8,
        intV (-1),
      ]), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/n/too-large" (#[
        .cell valueB,
        .slice s8A,
        .cell dictPair8,
        intV 1024,
      ]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/n/nan" (#[
        .cell valueB,
        .slice s8A,
        .cell dictPair8,
        .int .nan,
      ]), rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/type-dict-not-maybe-cell" (#[
        .cell valueA,
        .slice s8A,
        .tuple #[],
        intV 8,
      ]), rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/type-key-not-slice" (#[
        .cell valueA,
        .cell valueA,
        .cell dictPair8,
        intV 8,
      ]), rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/type-value-not-cell" (#[
        intV 7,
        .slice s8A,
        .cell dictPair8,
        intV 8,
      ]), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/key-too-short-n1" (#[
        .cell valueA,
        .slice s0,
        .cell dictSingle8,
        intV 1,
      ]), rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/key-too-short-n8" (#[
        .cell valueA,
        .slice s1,
        .cell dictSingle8,
        intV 8,
      ]), rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/key-too-short-1023" (#[
        .cell valueA,
        .slice s0,
        .null,
        intV 1023,
      ]), rng1)
    else if shape = 23 then
      (mkCase "fuzz/err/malformed-root" (#[
        .cell valueA,
        .slice s8A,
        .cell malformedDict,
        intV 8,
      ]), rng1)
    else if shape = 24 then
      (mkCase "fuzz/gas/base-exact-miss" #[
        .cell valueA,
        .slice s1023,
        .null,
        intV 1023,
      ]
        #[
          .pushInt (.num baseGas),
          .tonEnvOp .setGasLimit,
          instr
        ]
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 25 then
      (mkCase "fuzz/gas/base-exact-minus-one" #[
        .cell valueA,
        .slice s1023,
        .null,
        intV 1023,
      ]
        #[
          .pushInt (.num baseGasMinusOne),
          .tonEnvOp .setGasLimit,
          instr
        ]
        (oracleGasLimitsExactMinusOne baseGas), rng1)
    else if shape = 26 then
      (mkCase "fuzz/gas/hit-single-exact" #[
        .cell valueC,
        .slice s8A,
        .cell dictPair8,
        intV 8,
      ]
        #[
          .pushInt (.num hitPair8Gas),
          .tonEnvOp .setGasLimit,
          instr
        ]
        (oracleGasLimitsExact hitPair8Gas), rng1)
    else if shape = 27 then
      (mkCase "fuzz/gas/hit-shared4-exact" #[
        .cell valueC,
        .slice s4A,
        .cell dictShared4,
        intV 4,
      ]
        #[
          .pushInt (.num hitShared4Gas),
          .tonEnvOp .setGasLimit,
          instr
        ]
        (oracleGasLimitsExact hitShared4Gas), rng1)
    else if shape = 28 then
      (mkCodeCase "fuzz/raw/f423" (#[
        .cell valueA,
        .slice s8A,
        .cell dictSingle8,
        intV 8,
      ]) rawOpcodeF423, rng1)
    else
      (mkCodeCase "fuzz/raw/f422" (#[
        .cell valueA,
        .slice s8A,
        .cell dictSingle8,
        intV 8,
      ]) rawOpcodeF422, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st ←
          match runDICTREPLACEREFFallback (#[
            intV 1,
            intV 2,
            .slice s8A,
            .cell valueA
          ]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"fallback failed with {e}")
        if st == #[intV 1, intV 2, .slice s8A, .cell valueA, intV dispatchSentinel] then
          pure ()
        else
          throw (IO.userError s!"fallback failed: expected {reprStr #[intV 1, intV 2, .slice s8A, .cell valueA, intV dispatchSentinel]}, got {reprStr st}") },
    { name := "unit/encode-exact" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF423 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF423, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"encode failed: {e}") },
    { name := "unit/encode-reject-unsigned-non-int" -- [B8]
      run := do
        match assembleCp0 [.dictSet false true false .replace] with
        | .ok _ =>
            throw (IO.userError "invalid unsigned/non-int encoding accepted")
        | .error _ =>
            pure () },
    { name := "unit/decode/neighbors" -- [B9]
      run := do
        let s0 : Slice := Slice.ofCell rawOpcodeF423
        let _ ← expectDecodeStep "decode/f423" s0 (.dictSet false false true .replace) 16
        let s1 : Slice := Slice.ofCell rawOpcodeF422
        let _ ← expectDecodeStep "decode/f422" s1 (.dictSet false false false .replace) 16
        let s2 : Slice := Slice.ofCell rawOpcodeF424
        let _ ← expectDecodeStep "decode/f424" s2 (.dictSet true false false .replace) 16
        let s3 : Slice := Slice.ofCell rawOpcodeF425
        let _ ← expectDecodeStep "decode/f425" s3 (.dictSet true false true .replace) 16
        let s4 : Slice := Slice.ofCell rawOpcodeF426
        let _ ← expectDecodeStep "decode/f426" s4 (.dictSet true true false .replace) 16
        let s5 : Slice := Slice.ofCell rawOpcodeF427
        let s6 ← expectDecodeStep "decode/f427" s5 (.dictSet true true true .replace) 16
        if s6.bitsRemaining + s6.refsRemaining != 0 then
          throw (IO.userError "decode did not consume all bits") },
    { name := "unit/decode/truncated" -- [B9]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawOpcodeF4) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode-truncated: expected invOpcode, got {e}")
        | .ok (i, bits, _) =>
            throw (IO.userError s!"decode-truncated: expected failure, got {i} with {bits} bits") }
  ]
  oracle := #[
    mkCase "ok/hit/single8" (#[.cell valueB, .slice s8A, .cell dictSingle8, intV 8]) , -- [B5][B6]
    mkCase "ok/hit/single8-extra-bits" (#[.cell valueC, .slice sExtraA, .cell dictSingle8, intV 8]) , -- [B4][B6]
    mkCase "ok/hit/pair8-first" (#[.cell valueC, .slice s8A, .cell dictPair8, intV 8]) , -- [B5][B6]
    mkCase "ok/hit/pair8-second" (#[.cell valueA, .slice s8B, .cell dictPair8, intV 8]) , -- [B5][B6]
    mkCase "ok/hit/fork8" (#[.cell valueD, .slice s8C, .cell dictFork8, intV 8]) , -- [B5][B6]
    mkCase "ok/hit/single4" (#[.cell valueC, .slice s4A, .cell dictSingle4, intV 4]) , -- [B5][B6][B11]
    mkCase "ok/hit/shared4" (#[.cell valueA, .slice s4B, .cell dictShared4, intV 4]) , -- [B5][B6]
    mkCase "ok/hit/zero-width" (#[.cell valueD, .slice s8A, .cell dictSingle0, intV 0]) , -- [B11][B4]
    mkCase "ok/hit/max-width" (#[.cell valueA, .slice s1023, dictNull, intV 1023]) , -- [B11][B3][B4]
    mkCase "ok/miss/null" (#[.cell valueB, .slice s8A, dictNull, intV 8]) , -- [B5]
    mkCase "ok/miss/non-empty" (#[.cell valueC, .slice s8D, .cell dictSingle8, intV 8]) , -- [B5]
    mkCase "ok/miss/zero-width-empty" (#[.cell valueB, .slice s0, dictNull, intV 0]) , -- [B11][B4]
    mkCase "ok/miss/with-value-slice-trunc" (#[.cell valueC, .slice sShortA, .cell dictSingle8, intV 8]) , -- [B4]
    mkCase "err/underflow-empty" (#[]) , -- [B2]
    mkCase "err/underflow/one" #[intV 8] , -- [B2]
    mkCase "err/underflow/two" #[intV 8, .cell dictSingle8] , -- [B2]
    mkCase "err/underflow/three" #[intV 8, .cell dictSingle8, .slice s8A] , -- [B2]
    mkCase "err/type/dict-not-maybe-cell" (#[.cell valueA, .slice s8A, .tuple #[], intV 8]) , -- [B2]
    mkCase "err/type-key-not-slice" (#[.cell valueA, .cell valueB, .cell dictSingle8, intV 8]) , -- [B2][B4]
    mkCase "err/type-value-not-cell" (#[intV 7, .slice s8A, .cell dictSingle8, intV 8]) , -- [B6]
    mkCase "err/n/negative" (#[.cell valueA, .slice s8A, .cell dictSingle8, intV (-1)]) , -- [B3]
    mkCase "err/n/nan" (#[.cell valueA, .slice s8A, .cell dictSingle8, .int .nan]) , -- [B3]
    mkCase "err/n/too-large" (#[.cell valueA, .slice s8A, .cell dictSingle8, intV 1024]) , -- [B3]
    mkCase "err/key-too-short-n1" (#[.cell valueA, .slice s0, .cell dictSingle4, intV 1]) , -- [B4]
    mkCase "err/key-too-short-n4" (#[.cell valueA, .slice s1, .cell dictSingle4, intV 4]) , -- [B4]
    mkCase "err/key-too-short-n1023" (#[.cell valueA, .slice s0, .cell dictSingle8, intV 1023]) , -- [B4][B11]
    mkCase "err/dict-err-malformed-root" (#[.cell valueA, .slice s8A, .cell malformedDict, intV 8]) , -- [B7]
    mkCodeCase "ok/code/raw/f423" (#[.cell valueA, .slice s8A, .cell dictSingle8, intV 8]) rawOpcodeF423, -- [B9]
    mkCodeCase "ok/code/raw/f422" (#[.cell valueA, .slice s8A, .cell dictSingle8, intV 8]) rawOpcodeF422, -- [B9]
    mkCodeCase "ok/code/raw/f424" (#[.cell valueA, intV 5, .cell dictSingle8, intV 8]) rawOpcodeF424, -- [B9][B9]
    mkCodeCase "ok/code/raw/f425" (#[.cell valueA, intV 5, .cell dictSingle8, intV 8]) rawOpcodeF425, -- [B9][B9]
    mkCodeCase "ok/code/raw/f426" (#[.cell valueA, intV 5, .cell dictSingle8, intV 8]) rawOpcodeF426, -- [B9]
    mkCodeCase "ok/code/raw/f427" (#[.cell valueA, intV 5, .cell dictSingle8, intV 8]) rawOpcodeF427, -- [B9]
    mkCodeCase "err/code/raw/truncated8" (#[] : Array Value) rawOpcodeF4, -- [B9]
    mkCase "gas/base-exact-miss" (#[.cell valueA, .slice s8A, dictNull, intV 8]) (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact baseGas), -- [B10]
    mkCase "gas/base-exact-minus-one" (#[.cell valueA, .slice s8A, dictNull, intV 8]) (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne baseGas), -- [B10]
    mkCase "gas/hit-single-exact" (#[.cell valueB, .slice s8A, .cell dictPair8, intV 8]) (#[.pushInt (.num hitPair8Gas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitPair8Gas), -- [B10]
    mkCase "gas/hit-single-minus-one" (#[.cell valueB, .slice s8A, .cell dictPair8, intV 8]) (#[.pushInt (.num hitPair8GasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitPair8Gas), -- [B10]
    mkCase "gas/hit-shared4-exact" (#[.cell valueC, .slice s4A, .cell dictShared4, intV 4]) (#[.pushInt (.num hitShared4Gas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitShared4Gas), -- [B10]
    mkCase "gas/hit-shared4-minus-one" (#[.cell valueC, .slice s4A, .cell dictShared4, intV 4]) (#[.pushInt (.num hitShared4GasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitShared4Gas), -- [B10]
    mkCase "gas/hit-zero-exact" (#[.cell valueD, .slice s0, .cell dictSingle0, intV 0]) (#[.pushInt (.num hitZeroGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitZeroGas), -- [B10][B11]
    mkCase "gas/hit-zero-minus-one" (#[.cell valueD, .slice s0, .cell dictSingle0, intV 0]) (#[.pushInt (.num hitZeroGasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitZeroGas) -- [B10][B11]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTREPLACEREFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREPLACEREF
