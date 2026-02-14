import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETREF

/-
INSTRUCTION: DICTUGETREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path.
   - `.dictGet true true true` is only handled by `execInstrDictDictGet`; other instructions must delegate via `next`.

2. [B2] Stack arity and preflight operand checks.
   - `VM.checkUnderflow 3` requires dictionary, key, and `n`.
   - Fewer than 3 operands must throw `.stkUnd`.

3. [B3] `n` validation.
   - `popNatUpTo 1023` enforces integer `n` in `[0, 1023]`.
   - Negative values, `.nan`, or values larger than 1023 throw `.rangeChk`.

4. [B4] Key conversion and dictionary kind checks.
   - `popIntFinite` requires integer key (not `NaN`, not non-int type).
   - `popMaybeCell` accepts either a dictionary cell or `null`.
   - Non-int key gives `.typeChk`/`.intOv` through `popIntFinite`.
   - Negative or too-large unsigned keys are treated as out-of-range keys and map to miss.

5. [B5] Key conversion miss path.
   - For `.unsigned` integer keys, `dictKeyBits?` with given `n` returning `none` must not throw;
     execution pushes `0` and terminates.

6. [B6] Dict lookup hit/miss outcomes.
   - For key misses (`none` lookup result): push `0`.
   - For key hits: push found value as `.cell` and `-1`.
   - Existing non-lookup stack prefix is preserved.

7. [B7] By-ref value shape validation.
   - Hit requires value slice with `bitsRemaining = 0` and `refsRemaining = 1`.
   - Value that is not a pure reference-to-cell is `.dictErr`.

8. [B8] Dictionary structure errors.
   - Invalid dictionary roots or malformed nodes produce `.dictErr` from `dictLookupWithCells`.

9. [B9] Assembler behavior.
   - Valid encoding: `.dictGet true true true` -> `0xF40F`.
   - `.dictGet false true true` is invalid because unsigned requires `intKey = true` and must encode to `.invOpcode`.

10. [B10] Decoder behavior.
   - `0xF40A..0xF40F` decode to `.dictGet` forms.
   - `0xF409` and `0xF410` are out-of-range and decode to `.invOpcode`.
   - Truncated operands (e.g. 8-bit `0xF4`) must fail decode.

11. [B11] Gas accounting.
   - No variable create/cleanup branches in this instruction; only exact-gas-success and exact-minus-one-failure branches are relevant.

TOTAL BRANCHES: 11

Any branch not explicitly covered by an oracle test is handled by fuzz in this suite.
-/

private def suiteId : InstrId :=
  { name := "DICTUGETREF" }

private def instr : Instr :=
  .dictGet true true true

private def instrInvalid : Instr :=
  .dictGet false true true

private def rawF40A : Cell := Cell.mkOrdinary (natToBits 0xF40A 16) #[]
private def rawF40F : Cell := Cell.mkOrdinary (natToBits 0xF40F 16) #[]
private def rawGapLow : Cell := Cell.mkOrdinary (natToBits 0xF409 16) #[]
private def rawGapHigh : Cell := Cell.mkOrdinary (natToBits 0xF410 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def valueD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]

private def refA : Cell := Cell.mkOrdinary #[] #[valueA]
private def refB : Cell := Cell.mkOrdinary #[] #[valueB]
private def refC : Cell := Cell.mkOrdinary #[] #[valueC]
private def refD : Cell := Cell.mkOrdinary #[] #[valueD]

private def badValueBits : Cell := Cell.mkOrdinary (natToBits 0xF0 8) #[]
private def badValueRefs : Cell := Cell.mkOrdinary #[] #[valueA, valueB]
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictRootWithRef! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let bits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid unsigned key {k} for n={n}"
      match dictSetRefWithCells root bits v .set with
      | .ok (some root', _, _, _) => root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: insertion produced no root ({k}, n={n})"
      | .error e =>
          panic! s!"{label}: insert failed ({k}, n={n}): {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def dictU8 : Cell :=
  mkDictRootWithRef! "dict/u8" 8 #[(0, refA), (5, refB), (255, refC)]

private def dictU1 : Cell :=
  mkDictRootWithRef! "dict/u1" 1 #[(0, refA)]

private def dictU0 : Cell :=
  mkDictRootWithRef! "dict/u0" 0 #[(0, refD)]

private def dictBadValueBits : Cell :=
  mkDictRootWithRef! "dict/bad/bits" 8 #[(7, badValueBits)]

private def dictBadValueRefs : Cell :=
  mkDictRootWithRef! "dict/bad/refs" 8 #[(7, badValueRefs)]

private def exactGas : Int :=
  computeExactGasBudget instr

private def exactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

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

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGet .add (VM.push (intV 909)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGet instr stack

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (decoded, _, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {decoded}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def genDictUGetRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/n8" (#[ .null, intV 7, intV 8 ]), rng2)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/n257" (#[ .null, intV 4, intV 257 ]), rng2)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/n0" (#[ .null, intV 1, intV 0 ]), rng2)
    else if shape = 3 then
      (mkCase "fuzz/miss/narrow/1bit" (#[ .cell dictU1, intV 2, intV 1 ]), rng2)
    else if shape = 4 then
      (mkCase "fuzz/miss/narrow/key-overflow" (#[ .cell dictU1, intV 3, intV 1 ]), rng2)
    else if shape = 5 then
      (mkCase "fuzz/miss/key-negative" (#[ .cell dictU8, intV (-1), intV 8 ]), rng2)
    else if shape = 6 then
      (mkCase "fuzz/miss/key-too-large-for-n" (#[ .cell dictU8, intV 256, intV 8 ]), rng2)
    else if shape = 7 then
      (mkCase "fuzz/miss/key-not-present" (#[ .cell dictU8, intV 9, intV 8 ]), rng2)
    else if shape = 8 then
      (mkCase "fuzz/hit/key-0" (#[ .cell dictU8, intV 0, intV 8 ]), rng2)
    else if shape = 9 then
      (mkCase "fuzz/hit/key-5" (#[ .cell dictU8, intV 5, intV 8 ]), rng2)
    else if shape = 10 then
      (mkCase "fuzz/hit/key-255" (#[ .cell dictU8, intV 255, intV 8 ]), rng2)
    else if shape = 11 then
      (mkCase "fuzz/hit/n0" (#[ .cell dictU0, intV 0, intV 0 ]), rng2)
    else if shape = 12 then
      (mkCase "fuzz/hit/prefix-preserved" (#[ intV 77, .cell dictU8, intV 5, intV 8 ]), rng2)
    else if shape = 13 then
      (mkCase "fuzz/shape/type-key-null" (#[ .cell dictU8, .null, intV 8 ]), rng2)
    else if shape = 14 then
      (mkCase "fuzz/shape/type-key-cell" (#[ .cell dictU8, .cell Cell.empty, intV 8 ]), rng2)
    else if shape = 15 then
      (mkCase "fuzz/shape/type-key-slice" (#[ .cell dictU8, .slice (mkSliceFromBits (natToBits 0x1 1)), intV 8 ]), rng2)
    else if shape = 16 then
      (mkCase "fuzz/shape/key-nan" (#[ .cell dictU8, .int .nan, intV 8 ]), rng2)
    else if shape = 17 then
      (mkCase "fuzz/shape/type-dict-non-cell" (#[ .tuple #[], intV 5, intV 8 ]), rng2)
    else if shape = 18 then
      (mkCase "fuzz/shape/type-n-null" (#[ .cell dictU8, intV 5, .null ]), rng2)
    else if shape = 19 then
      (mkCase "fuzz/shape/type-n-builder" (#[ .cell dictU8, intV 5, .builder Builder.empty ]), rng2)
    else if shape = 20 then
      (mkCase "fuzz/shape/type-n-nan" (#[ .cell dictU8, intV 5, .int .nan ]), rng2)
    else if shape = 21 then
      (mkCase "fuzz/shape/n-negative" (#[ .cell dictU8, intV 5, intV (-1) ]), rng2)
    else if shape = 22 then
      (mkCase "fuzz/shape/n-too-large" (#[ .cell dictU8, intV 5, intV 1024 ]), rng2)
    else if shape = 23 then
      (mkCase "fuzz/shape/malformed-dict" (#[ .cell malformedDict, intV 5, intV 8 ]), rng2)
    else if shape = 24 then
      (mkCase "fuzz/shape/bad-value-bits" (#[ .cell dictBadValueBits, intV 7, intV 8 ]), rng2)
    else if shape = 25 then
      (mkCase "fuzz/shape/bad-value-refs" (#[ .cell dictBadValueRefs, intV 7, intV 8 ]), rng2)
    else if shape = 26 then
      (mkCase "fuzz/underflow/empty" (#[] : Array Value), rng2)
    else if shape = 27 then
      (mkCase "fuzz/underflow/one" #[.cell dictU8], rng2)
    else if shape = 28 then
      (mkCase "fuzz/underflow/two" #[.cell dictU8, intV 5], rng2)
    else
      (mkCase "fuzz/gas/exact"
        (#[ .cell dictU8, intV 5, intV 8 ])
        (#[ .pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr ])
        (oracleGasLimitsExact exactGas), rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

/--
    Oracle branch coverage is split so each major runtime branch has dedicated coverage,
    while raw-decoding and gas cases are represented in both unit and oracle sections.
--/


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st : Except Excno (Array Value) := runDispatchFallback #[]
        expectOkStack "dispatch/fallback" st (#[intV 909]) },
    { name := "unit/decode/valid-f40f" -- [B10]
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xF40F 16)
        let _ ← expectDecodeStep "decode/f40f" s instr 16 },
    { name := "unit/decode/invalid-bounds" -- [B10]
      run := do
        expectDecodeInvOpcode "decode/gap-low" 0xF409
        expectDecodeInvOpcode "decode/gap-high" 0xF410
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated expected failure") },
    { name := "unit/asm/encode" -- [B9]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF40F 16 then
              pure ()
            else
              throw (IO.userError s!"expected bits 0xF40F, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"expected assembly success, got {e}") },
    { name := "unit/asm/encode/reject-invalid-flags" -- [B9]
      run := do
        match assembleCp0 [instrInvalid] with
        | .ok _ =>
            throw (IO.userError "expected invOpcode, got success")
        | .error e =>
            if e != .invOpcode then
              throw (IO.userError s!"expected invOpcode, got {e}")
            else
              pure () },
    { name := "unit/runtime/hit-miss" -- [B3][B5][B6]
      run := do
        expectOkStack "miss/null" (runDirect (#[ .null, intV 7, intV 8 ])) (#[ intV 0 ])
        expectOkStack "hit/key-5" (runDirect (#[ .cell dictU8, intV 5, intV 8 ])) (#[ .cell refB, intV (-1) ])
        expectOkStack "hit/prefix-preserved"
          (runDirect (#[ intV 77, .cell dictU8, intV 5, intV 8 ]))
          (#[ intV 77, .cell refB, intV (-1) ])
        expectOkStack "out-of-range/negative" (runDirect (#[ .cell dictU8, intV (-1), intV 8 ])) (#[ intV 0 ]) },
    { name := "unit/runtime/errors" -- [B4][B7][B8]
      run := do
        expectErr "bad-value-bits" (runDirect (#[ .cell dictBadValueBits, intV 7, intV 8 ])) .dictErr
        expectErr "bad-value-refs" (runDirect (#[ .cell dictBadValueRefs, intV 7, intV 8 ])) .dictErr
        expectErr "malformed-dict" (runDirect (#[ .cell malformedDict, intV 5, intV 8 ])) .dictErr
        expectErr "n-negative" (runDirect (#[ .cell dictU8, intV 5, intV (-1) ])) .rangeChk
        expectErr "n-too-large" (runDirect (#[ .cell dictU8, intV 5, intV 1024 ])) .rangeChk
        expectErr "n-nan" (runDirect (#[ .cell dictU8, intV 5, .int .nan ])) .rangeChk
        expectErr "key-nan" (runDirect (#[ .cell dictU8, .int .nan, intV 8 ])) .intOv
        expectErr "key-type" (runDirect (#[ .cell dictU8, .cell Cell.empty, intV 8 ])) .typeChk
        expectErr "dict-type" (runDirect (#[ .tuple #[], intV 5, intV 8 ])) .typeChk
        expectErr "underflow-empty" (runDirect #[]) .stkUnd } ]
  oracle := #[
    -- [B2] Underflow cases.
    mkCase "oracle/err/underflow/0" #[],
    mkCase "oracle/err/underflow/1" #[.null],
    mkCase "oracle/err/underflow/2" #[.null, intV 0],

    -- [B3] n validation.
    mkCase "oracle/err/n-null" (#[ .cell dictU8, intV 5, .null ]),
    mkCase "oracle/err/n-builder" (#[ .cell dictU8, intV 5, .builder Builder.empty ]),
    mkCase "oracle/err/n-nan" (#[ .cell dictU8, intV 5, .int .nan ]),
    mkCase "oracle/err/n-negative" (#[ .cell dictU8, intV 5, intV (-1) ]),
    mkCase "oracle/err/n-too-large" (#[ .cell dictU8, intV 5, intV 1024 ]),

    -- [B4] Key and dict type checks.
    mkCase "oracle/err/key-null" (#[ .cell dictU8, .null, intV 8 ]),
    mkCase "oracle/err/key-cell" (#[ .cell dictU8, .cell Cell.empty, intV 8 ]),
    mkCase "oracle/err/key-slice" (#[ .cell dictU8, .slice (mkSliceFromBits (natToBits 0x1 1)), intV 8 ]),
    mkCase "oracle/err/key-nan" (#[ .cell dictU8, .int .nan, intV 8 ]),
    mkCase "oracle/err/dict-non-cell" (#[ .tuple #[], intV 5, intV 8 ]),

    -- [B5] Key conversion miss branches.
    mkCase "oracle/miss/key-negative" (#[ .cell dictU8, intV (-1), intV 8 ]),
    mkCase "oracle/miss/key-too-large" (#[ .cell dictU8, intV 256, intV 8 ]),
    mkCase "oracle/miss/narrow-width-mismatch" (#[ .cell dictU1, intV 2, intV 1 ]),
    mkCase "oracle/miss/n0-key-mismatch" (#[ .cell dictU0, intV 1, intV 0 ]),
    mkCase "oracle/miss/key-not-present" (#[ .cell dictU8, intV 9, intV 8 ]),
    mkCase "oracle/miss/null/n257" (#[ .null, intV 7, intV 257 ]),

    -- [B6] Lookup and stack-prefix behavior.
    mkCase "oracle/hit/key-0" (#[ .cell dictU8, intV 0, intV 8 ]),
    mkCase "oracle/hit/key-5" (#[ .cell dictU8, intV 5, intV 8 ]),
    mkCase "oracle/hit/key-255" (#[ .cell dictU8, intV 255, intV 8 ]),
    mkCase "oracle/hit/key-u0" (#[ .cell dictU0, intV 0, intV 0 ]),
    mkCase "oracle/hit/prefix-preserved" (#[ intV 42, .cell dictU8, intV 5, intV 8 ]),
    mkCase "oracle/miss/null" (#[ .null, intV 7, intV 8 ]),
    mkCase "oracle/miss/null-prefix-preserved" (#[ intV 99, .null, intV 5, intV 8 ]),

    -- [B7] By-ref value shape validation.
    mkCase "oracle/err/bad-value-bits" (#[ .cell dictBadValueBits, intV 7, intV 8 ]),
    mkCase "oracle/err/bad-value-refs" (#[ .cell dictBadValueRefs, intV 7, intV 8 ]),

    -- [B8] Dictionary structural errors.
    mkCase "oracle/err/malformed-dict" (#[ .cell malformedDict, intV 5, intV 8 ]),

    -- [B9][B10] Decode/assembly edge cases exercised via raw fixtures.
    mkCodeCase "oracle/code/f40a" #[] rawF40A,
    mkCodeCase "oracle/code/f40f" #[] rawF40F,
    mkCodeCase "oracle/code/f409-fail" #[] rawGapLow,
    mkCodeCase "oracle/code/f410-fail" #[] rawGapHigh,

    -- [B11] Gas exactness.
    mkCase "oracle/gas/exact-hit" (#[ .cell dictU8, intV 5, intV 8 ])
      (#[ .pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr ])
      (oracleGasLimitsExact exactGas),
    mkCase "oracle/gas/exact-minus-one-miss" (#[ .null, intV 5, intV 8 ])
      (#[ .pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr ])
      (oracleGasLimitsExactMinusOne exactGasMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictUGetRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETREF
