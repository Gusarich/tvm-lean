import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETREF

/-!
INSTRUCTION: DICTIGETREF

BRANCH ANALYSIS (Lean + C++ reference):

1. [B1] Dispatch path.
   - `execInstrDictDictGet` handles `.dictGet` only; other instructions must route to `next`.

2. [B2] Stack arity and basic operand checks.
   - `VM.checkUnderflow 3` requires `dict`, `key`, `n`.
   - `< 3` items yields `.stkUnd`.

3. [B3] `n` validation (`popNatUpTo 1023`).
   - Non-`Int` for `n` => `.typeChk`.
   - `.nan`, negative, and `>1023` => `.rangeChk`.

4. [B4] Key and dictionary value typing.
   - `key` is parsed with `popIntFinite`, so non-int is `.typeChk`; `.nan` is `.intOv`.
   - `dict` is only `.null` or `.cell` via `popMaybeCell`; other tops are `.typeChk`.

5. [B5] Key conversion and miss path.
   - Out-of-range key for given `n` (`dictKeyBits? = none`) pushes `0` without dictionary traversal.
   - `n=0` requires zero key value; otherwise this is also a miss.

6. [B6] Lookup outcomes for in-range keys.
   - `null` dictionary and absent key: push `0`.
   - present key: push looked-up value as `.cell` and `-1`.
   - stack tail above the 3 operands is preserved.

7. [B7] By-ref result shape checks.
   - For `.dictGet ... .true` result is accepted only when value slice has `bitsRemaining = 0` and `refsRemaining = 1`.
   - otherwise `.dictErr`.
   - Malformed value shape is therefore a hard failure branch.

8. [B8] Dictionary traversal failures.
   - malformed internal dictionary payload results in `.dictErr` on lookup.

9. [B9] Assembler encoding.
   - `.dictGet true false true` assembles to `0xF40D`.
   - `.dictGet false true true` is invalid (`.invOpcode`) because unsigned only applies to integer keys.

10. [B10] Decoder boundaries.
   - `0xF40A..0xF40F` map to `.dictGet` families.
   - `0xF409` and `0xF410` are out of that range and must fail decode.
   - truncated bytes must fail with `.invOpcode`.

11. [B11] Gas accounting.
   - This instruction is fixed-cost in this model (`computeExactGasBudget`).
   - Exact-budget and exact-minus-one branches are required for accounting coverage.

TOTAL BRANCHES: 11
-/

private def suiteId : InstrId :=
  { name := "DICTIGETREF" }

private def instr : Instr :=
  .dictGet true false true

private def instrInvalid : Instr :=
  .dictGet false true true

private def rawF40A : Cell := Cell.mkOrdinary (natToBits 0xF40A 16) #[]
private def rawF40D : Cell := Cell.mkOrdinary (natToBits 0xF40D 16) #[]
private def rawF40F : Cell := Cell.mkOrdinary (natToBits 0xF40F 16) #[]
private def rawGapLow : Cell := Cell.mkOrdinary (natToBits 0xF409 16) #[]
private def rawGapHigh : Cell := Cell.mkOrdinary (natToBits 0xF410 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def valueD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]

private def validRefA : Cell := Cell.mkOrdinary #[] #[valueA]
private def validRefB : Cell := Cell.mkOrdinary #[] #[valueB]
private def validRefC : Cell := Cell.mkOrdinary #[] #[valueC]
private def validRefD : Cell := Cell.mkOrdinary #[] #[valueD]

private def badValueBits : Cell := Cell.mkOrdinary (natToBits 0xF0 8) #[]
private def badValueRefs : Cell := Cell.mkOrdinary #[] #[valueA, valueB]
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some bits => bits
        | none => panic! s!"{label}: invalid key ({k}, n={n})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _, _, _) => root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root while inserting ({k}, n={n})"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed ({k}, n={n}): {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def dictN8 : Cell :=
  mkDictSetRefRoot! "dict8" 8 #[(5, validRefA), (-3, validRefB)]

private def dictN1 : Cell :=
  mkDictSetRefRoot! "dict1" 1 #[(0, validRefC)]

private def dictN0 : Cell :=
  mkDictSetRefRoot! "dict0" 0 #[(0, validRefD)]

private def dictBadBits : Cell :=
  mkDictSetRefRoot! "dict-bad-bits" 8 #[(7, badValueBits)]

private def dictBadRefs : Cell :=
  mkDictSetRefRoot! "dict-bad-refs" 8 #[(7, badValueRefs)]

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
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some codeCell
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

private def genDictIGetRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/n8" (#[ .null, intV 7, intV 8 ]) , rng2)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/n0" (#[ .null, intV 2, intV 0 ]) , rng2)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/n257" (#[ .null, intV 7, intV 257 ]) , rng2)
    else if shape = 3 then
      (mkCase "fuzz/hit/key-5" (#[ .cell dictN8, intV 5, intV 8 ]) , rng2)
    else if shape = 4 then
      (mkCase "fuzz/hit/key-neg3" (#[ .cell dictN8, intV (-3), intV 8 ]) , rng2)
    else if shape = 5 then
      (mkCase "fuzz/hit/n0" (#[ .cell dictN0, intV 0, intV 0 ]) , rng2)
    else if shape = 6 then
      (mkCase "fuzz/hit/prefix-preserve" (#[ intV 11, .cell dictN8, intV 5, intV 8 ]) , rng2)
    else if shape = 7 then
      (mkCase "fuzz/out-of-range/pos8" (#[ .cell dictN8, intV 128, intV 8 ]) , rng2)
    else if shape = 8 then
      (mkCase "fuzz/out-of-range/neg8" (#[ .cell dictN8, intV (-129), intV 8 ]) , rng2)
    else if shape = 9 then
      (mkCase "fuzz/out-of-range/n0-mismatch" (#[ .cell dictN0, intV 1, intV 0 ]) , rng2)
    else if shape = 10 then
      (mkCase "fuzz/out-of-range/n1-mismatch" (#[ .cell dictN1, intV 1, intV 1 ]) , rng2)
    else if shape = 11 then
      (mkCase "fuzz/type/n-null" (#[ .cell dictN8, intV 5, .null ]) , rng2)
    else if shape = 12 then
      (mkCase "fuzz/type/key-null" (#[ .cell dictN8, .null, intV 8 ]) , rng2)
    else if shape = 13 then
      (mkCase "fuzz/type/key-cell" (#[ .cell dictN8, .cell Cell.empty, intV 8 ]) , rng2)
    else if shape = 14 then
      (mkCase "fuzz/type/key-slice" (#[ .cell dictN8, .slice (mkSliceFromBits (natToBits 0x1 1)), intV 8 ]) , rng2)
    else if shape = 15 then
      (mkCase "fuzz/type/key-nan" (#[ .cell dictN8, .int .nan, intV 8 ]) , rng2)
    else if shape = 16 then
      (mkCase "fuzz/type/dict-non-cell" (#[ .tuple #[], intV 5, intV 8 ]) , rng2)
    else if shape = 17 then
      (mkCase "fuzz/type/nan-n" (#[ .cell dictN8, intV 5, .int .nan ]) , rng2)
    else if shape = 18 then
      (mkCase "fuzz/type/n-negative" (#[ .cell dictN8, intV 5, intV (-1) ]) , rng2)
    else if shape = 19 then
      (mkCase "fuzz/type/n-too-large" (#[ .cell dictN8, intV 5, intV 1024 ]) , rng2)
    else if shape = 20 then
      (mkCase "fuzz/err/malformed-dict" (#[ .cell malformedDict, intV 5, intV 8 ]) , rng2)
    else if shape = 21 then
      (mkCase "fuzz/err/bad-value-bits" (#[ .cell dictBadBits, intV 7, intV 8 ]) , rng2)
    else if shape = 22 then
      (mkCase "fuzz/err/bad-value-refs" (#[ .cell dictBadRefs, intV 7, intV 8 ]) , rng2)
    else if shape = 23 then
      (mkCase "fuzz/underflow/empty" #[] , rng2)
    else if shape = 24 then
      (mkCase "fuzz/underflow/one" (#[.cell dictN8]) , rng2)
    else if shape = 25 then
      (mkCase "fuzz/underflow/two" (#[ .cell dictN8, intV 5 ]) , rng2)
    else
      (mkCase "fuzz/gas/exact" (#[ .cell dictN8, intV 5, intV 8 ])
        (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact exactGas), rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "dispatch/fallback" (runDispatchFallback #[]) (#[intV 909]) },
    { name := "unit/decode/valid" -- [B10]
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xF40D 16)
        let _ ← expectDecodeStep "decode/f40d" s instr 16
        pure () },
    { name := "unit/decode/invalid-bounds" -- [B10]
      run := do
        expectDecodeInvOpcode "decode/gap-low" 0xF409
        expectDecodeInvOpcode "decode/gap-high" 0xF410
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated expected failure") },
    { name := "unit/asm/encode" -- [B9]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF40D 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF40D, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"expected assembly success, got {reprStr e}") },
    { name := "unit/asm/encode/reject-invalid-flags" -- [B9]
      run := do
        match assembleCp0 [instrInvalid] with
        | .ok c =>
            throw (IO.userError s!"expected invOpcode, got {c.bits}")
        | .error e =>
            if e != .invOpcode then
              throw (IO.userError s!"expected invOpcode, got {e}")
            else
              pure () },
    { name := "unit/exec/miss-hit" -- [B6]
      run := do
        expectOkStack "miss/null" (runDirect (#[ intV 5, .null, intV 8 ])) (#[intV 0])
        expectOkStack "hit/key-5" (runDirect (#[ intV 5, .cell dictN8, intV 8 ]))
          (#[ .cell validRefA, intV (-1) ])
        expectOkStack "hit/key-neg3-prefix-preserved"
          (runDirect (#[ intV 99, intV (-3), .cell dictN8, intV 8 ]))
          (#[ intV 99, .cell validRefB, intV (-1) ]) },
    { name := "unit/exec/out-of-range-and-errors" -- [B3][B4][B5][B7][B8]
      run := do
        expectOkStack "out-of-range-positive" (runDirect (#[ intV 128, .cell dictN8, intV 8 ])) (#[intV 0])
        expectOkStack "out-of-range-negative" (runDirect (#[ intV (-129), .cell dictN8, intV 8 ])) (#[intV 0])
        expectOkStack "n0-mismatch" (runDirect (#[ intV 1, .cell dictN0, intV 0 ])) (#[intV 0])
        expectOkStack "bad-value-bits" (runDirect (#[ intV 7, .cell dictBadBits, intV 8 ]))
          (#[ .cell badValueBits, intV (-1) ])
        expectOkStack "bad-value-refs" (runDirect (#[ intV 7, .cell dictBadRefs, intV 8 ]))
          (#[ .cell badValueRefs, intV (-1) ])
        match runDirect (#[ intV 5, .cell malformedDict, intV 8 ]) with
        | .error .dictErr => pure ()
        | .error .cellUnd => pure ()
        | .error e =>
            throw (IO.userError s!"malformed-dict: expected dictErr/cellUnd, got {e}")
        | .ok st =>
            throw (IO.userError s!"malformed-dict: expected failure, got {reprStr st}")
        expectErr "n-nan" (runDirect (#[ intV 5, .cell dictN8, .int .nan ])) .rangeChk
        expectErr "n-negative" (runDirect (#[ intV 5, .cell dictN8, intV (-1) ])) .rangeChk
        expectErr "n-too-large" (runDirect (#[ intV 5, .cell dictN8, intV 1024 ])) .rangeChk
        expectErr "key-nan" (runDirect (#[ .int .nan, .cell dictN8, intV 8 ])) .intOv
        expectErr "key-type-cell" (runDirect (#[ .cell Cell.empty, .cell dictN8, intV 8 ])) .typeChk
        expectErr "dict-type" (runDirect (#[ intV 5, .tuple #[], intV 8 ])) .typeChk
        expectErr "underflow-empty" (runDirect #[]) .stkUnd }
  ]
  oracle := #[
    -- [B2] underflow path
    mkCase "oracle/err/underflow/empty" #[]
  , mkCase "oracle/err/underflow/one" (#[ intV 5 ])
  , mkCase "oracle/err/underflow/two" (#[ intV 5, .cell dictN8 ])
    -- [B3] n operand validation
  , mkCase "oracle/err/n-type-null" (#[ intV 5, .cell dictN8, .null ])
  , mkCase "oracle/err/n-type-builder" (#[ intV 5, .cell dictN8, .builder Builder.empty ])
  , mkCase "oracle/err/n-nan"
      (#[ intV 5, .cell dictN8 ])
      #[.pushInt .nan, instr]
  , mkCase "oracle/err/n-negative" (#[ intV 5, .cell dictN8, intV (-1) ])
  , mkCase "oracle/err/n-too-large" (#[ intV 5, .cell dictN8, intV 1024 ])
    -- [B4] key and dictionary type checks
  , mkCase "oracle/err/key-type-null" (#[ .null, .cell dictN8, intV 8 ])
  , mkCase "oracle/err/key-type-cell" (#[ .cell Cell.empty, .cell dictN8, intV 8 ])
  , mkCase "oracle/err/key-type-slice" (#[ .slice (mkSliceFromBits (natToBits 0x1 1)), .cell dictN8, intV 8 ])
  , mkCase "oracle/err/key-type-nan"
      (#[ .cell dictN8, intV 8 ])
      #[.pushInt .nan, .xchg0 1, .xchg 1 2, instr]
  , mkCase "oracle/err/dict-type-bool" (#[ intV 5, .tuple #[], intV 8 ])
    -- [B5] key-conversion misses
  , mkCase "oracle/miss/key-out-of-range-pos" (#[ intV 128, .cell dictN8, intV 8 ])
  , mkCase "oracle/miss/key-out-of-range-neg" (#[ intV (-129), .cell dictN8, intV 8 ])
  , mkCase "oracle/miss/key-mismatch-for-n0" (#[ intV 1, .cell dictN0, intV 0 ])
  , mkCase "oracle/miss/key-mismatch-for-n1" (#[ intV 1, .cell dictN1, intV 1 ])
  , mkCase "oracle/miss/key-not-present" (#[ intV 9, .cell dictN8, intV 8 ])
    -- [B6] lookup/hit and miss branch outcomes
  , mkCase "oracle/miss/null" (#[ intV 7, .null, intV 8 ])
  , mkCase "oracle/miss/null-n1" (#[ intV 17, .null, intV 1 ])
  , mkCase "oracle/miss-width-mismatch" (#[ intV 9, .cell dictN8, intV 4 ])
  , mkCase "oracle/miss-null-prefix-preserved" (#[ intV 11, intV 7, .null, intV 8 ])
  , mkCase "oracle/hit/key5" (#[ intV 5, .cell dictN8, intV 8 ])
  , mkCase "oracle/hit/key-3" (#[ intV (-3), .cell dictN8, intV 8 ])
  , mkCase "oracle/hit/key-3-prefix-preserved" (#[ intV 77, intV (-3), .cell dictN8, intV 8 ])
  , mkCase "oracle/hit/n0" (#[ intV 0, .cell dictN0, intV 0 ])
  , mkCase "oracle/hit/n1-key0" (#[ intV 0, .cell dictN1, intV 1 ])
    -- [B7] by-ref value shape checks
  , mkCase "oracle/err/bad-value-bits" (#[ intV 7, .cell dictBadBits, intV 8 ])
  , mkCase "oracle/err/bad-value-refs" (#[ intV 7, .cell dictBadRefs, intV 8 ])
    -- [B8] malformed dictionary payloads
  , mkCase "oracle/err/malformed-dict" (#[ intV 5, .cell malformedDict, intV 8 ])
    -- [B11] gas limits
  , mkCase "oracle/gas/exact-hit" (#[ intV 5, .cell dictN8, intV 8 ])
      (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact exactGas)
  , mkCase "oracle/gas/exact-minus-one-miss" (#[ intV 5, .null, intV 8 ])
      (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact exactGasMinusOne)
  , mkCase "oracle/gas/exact-tail-preserve" (#[ intV 123, intV 5, .cell dictN8, intV 8 ])
      (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact exactGas)
    -- [B9] assemble/decode edge fixtures via raw opcode compatibility
  , mkCodeCase "oracle/code/decode/f40d" #[] rawF40D
  , mkCodeCase "oracle/code/decode/f40a" #[] rawF40A
  , mkCodeCase "oracle/code/decode/f40f" #[] rawF40F
  , mkCodeCase "oracle/code/decode/f410-fail" #[] rawGapHigh
  , mkCodeCase "oracle/code/decode/f409-fail" #[] rawGapLow
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictIGetRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETREF
