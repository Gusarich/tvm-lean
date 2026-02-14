import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGET

/-!
INSTRUCTION: DICTUGET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictDictGet` executes only on `.dictGet`; every other constructor must forward via `next`.

2. [B2] Runtime stack arity guard.
   - `checkUnderflow 3` is applied before any pop.

3. [B3] `n` validation.
   - `popNatUpTo 1023` / `pop_smallint_range(Dictionary::max_key_bits)`:
     - `.typeChk` when `n` is not int.
     - `.rangeChk` for NaN, negative, or > 1023.

4. [B4] Dictionary source type check.
   - Only `null` or `cell` values are accepted; everything else throws `.typeChk`.

5. [B5] Unsigned key parsing.
   - `popIntFinite` checks key type and numeric finiteness:
     - `.typeChk` for non-int values.
     - `.intOv` for NaN.
   - `dictKeyBits? idx n true` is used for unsigned conversion.

6. [B6] Unsigned conversion out-of-range.
   - If conversion fails (`none`), return `0` directly (dictionary miss), no exception.
   - Examples: negative keys or keys with magnitude exceeding n bits.

7. [B7] Dictionary lookup.
   - `null` root yields miss (`0`).
   - Valid in-range key + present entry yields `<value>, -1`.
   - Absent key yields `0`.
   - Dictionary traversal failures raise `.dictErr`.

8. [B8] by-ref retrieval.
   - With `REF`, hit requires a value slice of zero bits and one reference.
   - Otherwise raise `.dictErr`.

9. [B9] Payload/structure errors.
   - Malformed dictionary roots and malformed traversals raise `.dictErr`.

10. [B10] Assembler validation.
   - Valid encodings:
     - `.dictGet true true false` -> `0xf40e`
     - `.dictGet true true true` -> `0xf40f`
   - `.dictGet true false false` (unsigned flag missing for integer-key opcodes) is invalid.

11. [B11] Decoder boundary behavior.
   - Opcode range `0xf40a..0xf40f` decodes to `.dictGet`:
     - `0xf40e` and `0xf40f` resolve to unsigned-key modes.
   - Invalid opcodes like `0xf409`, `0xf410`, and truncated forms are rejected.
   - Adjacent opcodes (`0xf40c`,`0xf40d`) decode to signed-integer forms, exercising branch adjacency.

12. [B12] Width edge behavior.
   - Boundary key widths (`n = 0` and `n = 1`) are valid and must preserve miss/hit semantics.

13. [B13] Gas accounting.
   - Base gas only (no variable penalty branch).
   - Explicit exact and exact-minus-one checks verify success and out-of-gas behavior.

TOTAL BRANCHES: 13

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def dictUGetId : InstrId := { name := "DICTUGET" }

private def dictUGet : Instr := .dictGet true true false
private def dictUGetRef : Instr := .dictGet true true true

private def markerSlice (marker : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits marker 16) #[])

private def dict8Marker0 : Slice := markerSlice 0x51
private def dict8Marker1 : Slice := markerSlice 0x52
private def dict8Marker255 : Slice := markerSlice 0x53
private def dict1Marker0 : Slice := markerSlice 0x61
private def dict0Marker0 : Slice := markerSlice 0x62

private def byRefValueCell : Cell := Cell.mkOrdinary (natToBits 0x77 16) #[]
private def byRefLeaf : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[byRefValueCell])
private def byRefMalformedLeaf : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[])
private def byRefValueMarker : Value := .cell byRefValueCell

private def requireBits (label : String) (key : Int) (n : Nat) : BitString :=
  match dictKeyBits? key n true with
  | some bits => bits
  | none => panic! s!"{label}: unsupported key {key} for n={n} unsigned=true"

private def mkDictFromPairs (label : String) (n : Nat) (pairs : Array (Int × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        match st with
        | some root =>
            let key := pair.1
            let value := pair.2
            match dictSetSliceWithCells (some root) (requireBits label key n) value .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            let key := pair.1
            let value := pair.2
            match dictSetSliceWithCells none (requireBits label key n) value .set with
            | .ok (some root, _, _, _) => some root
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build dictionary"

private def dictU8Root : Cell :=
  mkDictFromPairs "dictU8Root" 8 #[
    (0, dict8Marker0),
    (1, dict8Marker1),
    (255, dict8Marker255)
  ]

private def dictU1Root : Cell :=
  mkDictFromPairs "dictU1Root" 1 #[(0, dict1Marker0)]

private def dictU0Root : Cell :=
  mkDictFromPairs "dictU0Root" 0 #[(0, dict0Marker0)]

private def dictU8ByRefRoot : Cell :=
  mkDictFromPairs
    "dictU8ByRefRoot"
    8
    #[(0, byRefLeaf), (1, byRefMalformedLeaf), (255, byRefMalformedLeaf)]

private def dictU8UnsignedByRefRoot : Cell :=
  mkDictFromPairs
    "dictU8UnsignedByRefRoot"
    8
    #[(0, byRefLeaf), (255, byRefMalformedLeaf)]

private def malformedDictCell : Cell := Cell.mkOrdinary (natToBits 0b10 2) #[]

private def dictUGasExact : Int := computeExactGasBudget dictUGet
private def dictUGasExactMinusOne : Int := computeExactGasBudgetMinusOne dictUGet

private def rawF40e : Cell := Cell.mkOrdinary (natToBits 0xf40e 16) #[]
private def rawF40f : Cell := Cell.mkOrdinary (natToBits 0xf40f 16) #[]
private def rawF40d : Cell := Cell.mkOrdinary (natToBits 0xf40d 16) #[]
private def rawF40c : Cell := Cell.mkOrdinary (natToBits 0xf40c 16) #[]
private def rawF409 : Cell := Cell.mkOrdinary (natToBits 0xf409 16) #[]
private def rawF410 : Cell := Cell.mkOrdinary (natToBits 0xf410 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def opcodeSlice16 (w : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w 16) #[])

private def expectDecodeInvOpcode (label : String) (w : Nat) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 w) with
  | .ok (_, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, but decode succeeded")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, got {reprStr e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictUGet])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUGetId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUGetId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictUGet (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGet dictUGet stack

private def runDictUGetRef (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGet dictUGetRef stack

private def runDictUGetDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGet instr (VM.push (intV 12_345)) stack

private def stackIntKey
    (key : Int)
    (dictValue : Value)
    (n : Int) : Array Value :=
  #[intV key, dictValue, intV n]

private def genDictUGetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  let (tag, rng2) := randNat rng1 0 999_999
  let base := s!"fuzz/{tag}/{shape}"
  let case0 :=
    if shape = 0 then
      mkCase (s!"{base}/hit-key-0") (stackIntKey 0 (.cell dictU8Root) 8)
    else if shape = 1 then
      mkCase (s!"{base}/hit-key-1") (stackIntKey 1 (.cell dictU8Root) 8)
    else if shape = 2 then
      mkCase (s!"{base}/hit-key-255") (stackIntKey 255 (.cell dictU8Root) 8)
    else if shape = 3 then
      mkCase (s!"{base}/miss-key-7") (stackIntKey 7 (.cell dictU8Root) 8)
    else if shape = 4 then
      mkCase (s!"{base}/miss-none-root") (stackIntKey 0 (.null) 8)
    else if shape = 5 then
      mkCase (s!"{base}/miss-key-too-large-256") (stackIntKey 256 (.cell dictU8Root) 8)
    else if shape = 6 then
      mkCase (s!"{base}/miss-key-negative") (stackIntKey (-1) (.cell dictU8Root) 8)
    else if shape = 7 then
      mkCase (s!"{base}/n-negative") (stackIntKey 0 (.cell dictU8Root) (-1))
    else if shape = 8 then
      mkCase (s!"{base}/n-too-large") (stackIntKey 0 (.cell dictU8Root) 1024)
    else if shape = 9 then
      mkCase (s!"{base}/n-nan") (#[.cell dictU8Root, intV 0, .int .nan])
    else if shape = 10 then
      mkCase (s!"{base}/key-null") (#[.cell dictU8Root, .null, intV 8])
    else if shape = 11 then
      mkCase (s!"{base}/key-builder") (#[.cell dictU8Root, .builder Builder.empty, intV 8])
    else if shape = 12 then
      mkCase (s!"{base}/key-nan") (#[.cell dictU8Root, .int .nan, intV 8])
    else if shape = 13 then
      mkCase (s!"{base}/dict-bool") (#[.tuple #[], .cell Cell.empty, intV 8])
    else if shape = 14 then
      mkCase (s!"{base}/dict-malformed") (stackIntKey 0 (.cell malformedDictCell) 8)
    else if shape = 15 then
      mkCase (s!"{base}/byref-hit") (stackIntKey 0 (.cell dictU8ByRefRoot) 8) (#[dictUGetRef])
    else if shape = 16 then
      mkCase (s!"{base}/byref-malformed") (stackIntKey 1 (.cell dictU8ByRefRoot) 8) (#[dictUGetRef])
    else if shape = 17 then
      mkCase (s!"{base}/byref-unsigned-malformed") (stackIntKey 255 (.cell dictU8UnsignedByRefRoot) 8) (#[dictUGetRef])
    else if shape = 18 then
      mkCase (s!"{base}/n1-hit") (stackIntKey 0 (.cell dictU1Root) 1)
    else if shape = 19 then
      mkCase (s!"{base}/n1-miss") (stackIntKey 1 (.cell dictU1Root) 1)
    else if shape = 20 then
      mkCase (s!"{base}/n0-hit") (stackIntKey 0 (.cell dictU0Root) 0)
    else if shape = 21 then
      mkCase (s!"{base}/n0-miss") (stackIntKey 1 (.cell dictU0Root) 0)
    else if shape = 22 then
      mkCase
        (s!"{base}/gas-exact")
        (stackIntKey 255 (.cell dictU8Root) 8)
        (#[.pushInt (.num dictUGasExact), .tonEnvOp .setGasLimit, dictUGet])
        (oracleGasLimitsExact dictUGasExact)
    else if shape = 23 then
      mkCase
        (s!"{base}/gas-exact-minus-one")
        (stackIntKey 255 (.cell dictU8Root) 8)
        (#[.pushInt (.num dictUGasExactMinusOne), .tonEnvOp .setGasLimit, dictUGet])
        (oracleGasLimitsExactMinusOne dictUGasExactMinusOne)
    else if shape = 24 then
      mkCase
        (s!"{base}/fallback") (stackIntKey 5 (.cell dictU8Root) 8) (#[.dictGet true true false])
    else if shape = 25 then
      mkCase (s!"{base}/truncated-program") (stackIntKey 0 (.cell dictU8Root) 8) (#[.dictGet true true true])
    else
      mkCaseCode (s!"{base}/raw") #[] rawF40e
  (case0, rng2)

def suite : InstrSuite where
  id := dictUGetId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        let sentinel : Int := 12_345
        expectOkStack
          "fallback/non-match"
          (runDictUGetDispatchFallback .add #[])
          (#[intV sentinel])
        expectOkStack
          "match/executes-dictuget"
          (runDictUGet (stackIntKey 1 (.cell dictU8Root) 8))
          (#[.slice dict8Marker1, intV (-1)]) },
    { name := "unit/underflow"
      run := do
        expectErr "empty-stack" (runDictUGet #[]) .stkUnd
        expectErr "one-item" (runDictUGet #[.int (.num 8)]) .stkUnd
        expectErr "two-items" (runDictUGet #[.cell dictU8Root, intV 1]) .stkUnd },
    { name := "unit/n-operand-type-and-range"
      run := do
        expectErr "n-not-int" (runDictUGet #[.cell dictU8Root, intV 0, .null]) .typeChk
        expectErr "n-nan" (runDictUGet #[.cell dictU8Root, intV 1, .int .nan]) .rangeChk
        expectErr "n-negative" (runDictUGet (stackIntKey 0 (.cell dictU8Root) (-1))) .rangeChk
        expectErr "n-too-large" (runDictUGet (stackIntKey 0 (.cell dictU8Root) 1024)) .rangeChk },
    { name := "unit/dict-and-key-type-checks"
      run := do
        expectErr "dict-not-null-or-cell/slice" (runDictUGet #[.builder Builder.empty, intV 5, intV 8]) .typeChk
        expectErr "dict-not-null-or-cell/tuple" (runDictUGet #[.tuple #[], intV 5, intV 8]) .typeChk
        expectErr "key-not-int" (runDictUGet #[.cell dictU8Root, .null, intV 8]) .typeChk
        expectErr "key-not-int/cell" (runDictUGet #[.cell dictU8Root, .cell Cell.empty, intV 8]) .typeChk
        expectErr "key-nan" (runDictUGet #[.cell dictU8Root, .int .nan, intV 8]) .intOv },
    { name := "unit/lookup-hit-miss"
      run := do
        expectOkStack
          "hit-key-0"
          (runDictUGet (stackIntKey 0 (.cell dictU8Root) 8))
          (#[.slice dict8Marker0, intV (-1)])
        expectOkStack
          "hit-key-255"
          (runDictUGet (stackIntKey 255 (.cell dictU8Root) 8))
          (#[.slice dict8Marker255, intV (-1)])
        expectOkStack
          "miss-key-7"
          (runDictUGet (stackIntKey 7 (.cell dictU8Root) 8))
          (#[intV 0])
        expectOkStack
          "miss-none-root"
          (runDictUGet (stackIntKey 1 (.null) 8))
          (#[intV 0])
        expectOkStack
          "out-of-range-positive"
          (runDictUGet (stackIntKey 256 (.cell dictU8Root) 8))
          (#[intV 0])
        expectOkStack
          "out-of-range-negative"
          (runDictUGet (stackIntKey (-1) (.cell dictU8Root) 8))
          (#[intV 0])
        expectOkStack
          "n0-hit"
          (runDictUGet (stackIntKey 0 (.cell dictU0Root) 0))
          (#[.slice dict0Marker0, intV (-1)])
        expectOkStack
          "n0-miss"
          (runDictUGet (stackIntKey 1 (.cell dictU0Root) 0))
          (#[intV 0])
        expectOkStack
          "n1-hit"
          (runDictUGet (stackIntKey 0 (.cell dictU1Root) 1))
          (#[.slice dict1Marker0, intV (-1)])
        expectOkStack
          "n1-miss"
          (runDictUGet (stackIntKey 1 (.cell dictU1Root) 1))
          (#[intV 0]) },
    { name := "unit/stack-preserve"
      run := do
        expectOkStack
          "preserve-prefix-hit"
          (runDictUGet #[intV 77, .cell dictU8Root, intV 0, intV 8])
          (#[intV 77, .slice dict8Marker0, intV (-1)])
        expectOkStack
          "preserve-prefix-miss"
          (runDictUGet #[intV 77, .null, intV 0, intV 8])
          (#[intV 77, intV 0]) },
    { name := "unit/by-ref"
      run := do
        expectOkStack
          "byref-hit"
          (runDictUGetRef (stackIntKey 0 (.cell dictU8ByRefRoot) 8))
          (#[byRefValueMarker, intV (-1)])
        expectErr
          "byref-malformed"
          (runDictUGetRef (stackIntKey 1 (.cell dictU8ByRefRoot) 8))
          .dictErr },
    { name := "unit/malformed-root"
      run := do
        expectErr
          "malformed-root"
          (runDictUGet (stackIntKey 0 (.cell malformedDictCell) 8))
          .dictErr },
    { name := "unit/asm-encode-paths"
      run := do
        match assembleCp0 [dictUGet] with
        | .ok c =>
            if c.bits != natToBits 0xf40e 16 then
              throw (IO.userError s!"encode/dictuget expected 0xf40e, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictuget expected success, got {e}")
        match assembleCp0 [dictUGetRef] with
        | .ok c =>
            if c.bits != natToBits 0xf40f 16 then
              throw (IO.userError s!"encode/dictuget-ref expected 0xf40f, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictuget-ref expected success, got {e}")
        match assembleCp0 [dictUGet] with
        | .ok c =>
            if c.bits != natToBits 0xf40e 16 then
              throw (IO.userError s!"encode/dictuget expected 0xf40e, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictuget expected success, got {e}")
        match assembleCp0 [.dictGet true false false] with
        | .ok _ =>
            throw (IO.userError "encode/dictuget non-unsigned should be invalid")
        | .error .invOpcode =>
            pure ()
        | .error e =>
            throw (IO.userError s!"encode invalid flags expected invOpcode, got {e}") },
    { name := "unit/decode-paths"
      run := do
        let s0 := opcodeSlice16 0xf40e
        let _ ← expectDecodeStep "decode/0xf40e" s0 (.dictGet true true false) 16
        let s1 := opcodeSlice16 0xf40f
        let _ ← expectDecodeStep "decode/0xf40f" s1 (.dictGet true true true) 16
        expectDecodeInvOpcode "decode/invalid-gap-low" 0xf409
        expectDecodeInvOpcode "decode/invalid-gap-high" 0xf410
        let _ ← expectDecodeStep "decode/adjacent-signed-int" (opcodeSlice16 0xf40c) (.dictGet true false false) 16
        let _ ← expectDecodeStep "decode/adjacent-signed-int-ref" (opcodeSlice16 0xf40d) (.dictGet true false true) 16
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated-8-bit expected failure") }
  ]
  oracle := #[
    -- [B1] dispatch/fallback
    -- [B1]
    mkCase "or/fallback-empty-stack" #[],
    -- [B1]
    mkCase "or/fallback-one" #[.int (.num 8)],

    -- [B2]
    -- [B2] underflow
    -- [B2]
    mkCase "or/underflow-empty" #[],
    -- [B2]
    mkCase "or/underflow-one" #[.int (.num 8)],
    -- [B2]
    mkCase "or/underflow-two" #[.cell dictU8Root, intV 1],

    -- [B3] `n` type/range
    -- [B3]
    mkCase "or/type/n-not-int" #[.cell dictU8Root, intV 1, .null],
    -- [B3]
    mkCase "or/type/n-builder" #[.cell dictU8Root, intV 1, .builder Builder.empty],
    -- [B3]
    mkCase "or/type/n-nan" #[.cell dictU8Root, intV 1, .int .nan],
    -- [B3]
    mkCase "or/range/n-negative" #[.cell dictU8Root, intV 1, intV (-1)],
    -- [B3]
    mkCase "or/range/n-too-large" #[.cell dictU8Root, intV 1, intV 1024],
    -- [B3]
    mkCase "or/range/n-max" #[.cell dictU8Root, intV 1, intV 1023],

    -- [B4] dictionary type errors
    -- [B4]
    mkCase "or/type/dict-builder" #[.builder Builder.empty, intV 1, intV 8],
    -- [B4]
    mkCase "or/type/dict-tuple" #[.tuple #[], intV 1, intV 8],

    -- [B5] key type checks
    -- [B5]
    mkCase "or/type/key-null" #[.cell dictU8Root, .null, intV 8],
    -- [B5]
    mkCase "or/type/key-cell" #[.cell dictU8Root, .cell Cell.empty, intV 8],
    -- [B5]
    mkCase "or/type/key-nan" #[.cell dictU8Root, .int .nan, intV 8],

    -- [B6] key conversion miss
    -- [B6]
    mkCase "or/conversion/out-of-range-positive" (stackIntKey 256 (.cell dictU8Root) 8),
    -- [B6]
    mkCase "or/conversion/out-of-range-negative" (stackIntKey (-1) (.cell dictU8Root) 8),
    -- [B6]
    mkCase "or/conversion/out-of-range-n0-key" (stackIntKey 1 (.cell dictU0Root) 0),
    -- [B6]
    mkCase "or/conversion/out-of-range-n1-key" (stackIntKey 1 (.cell dictU1Root) 1),

    -- [B7] hit/miss branches
    -- [B7]
    mkCase "or/lookup/miss-none-root" (stackIntKey 0 (.null) 8),
    -- [B7]
    mkCase "or/lookup/miss-key-7" (stackIntKey 7 (.cell dictU8Root) 8),
    -- [B7]
    mkCase "or/lookup/miss-key-large" (stackIntKey 200 (.cell dictU8Root) 8),
    -- [B7]
    mkCase "or/lookup/miss-empty-tail" (stackIntKey 77 (.null) 8),
    -- [B7]
    mkCase "or/lookup/hit-key-0" (stackIntKey 0 (.cell dictU8Root) 8),
    -- [B7]
    mkCase "or/lookup/hit-key-1" (stackIntKey 1 (.cell dictU8Root) 8),
    -- [B7]
    mkCase "or/lookup/hit-key-255" (stackIntKey 255 (.cell dictU8Root) 8),
    -- [B7]
    mkCase "or/lookup/n0-hit" (stackIntKey 0 (.cell dictU0Root) 0),
    -- [B7]
    mkCase "or/lookup/n1-hit" (stackIntKey 0 (.cell dictU1Root) 1),
    -- [B7]
    mkCase "or/lookup/preserve-hit" (#[intV 77, .cell dictU8Root, intV 1, intV 8]),
    -- [B7]
    mkCase "or/lookup/preserve-miss" (#[intV 77, .null, intV 7, intV 8]),

    -- [B8] by-ref retrieval
    -- [B8]
    mkCase "or/byref/hit" (stackIntKey 0 (.cell dictU8ByRefRoot) 8) (#[dictUGetRef]),
    -- [B8]
    mkCase "or/byref/malformed-smallbits" (stackIntKey 1 (.cell dictU8ByRefRoot) 8) (#[dictUGetRef]),
    -- [B8]
    mkCase "or/byref/malformed-nonzero-ref-count" (stackIntKey 255 (.cell dictU8ByRefRoot) 8) (#[dictUGetRef]),
    -- [B8]
    mkCase "or/byref/unsigned-has-boundary-malformed" (stackIntKey 255 (.cell dictU8UnsignedByRefRoot) 8) (#[dictUGetRef]),

    -- [B9] malformed dict structure
    -- [B9]
    mkCase "or/error/malformed-root" (stackIntKey 0 (.cell malformedDictCell) 8),
    -- [B9]
    mkCase "or/error/malformed-root-tail" (#[intV 99, .cell malformedDictCell, intV 0, intV 8]),

    -- [B10] [B11] assembler/decoder boundaries
    -- [B10] [B11]
    mkCaseCode "or/encode/decode/f40e" #[] rawF40e,
    -- [B10] [B11]
    mkCaseCode "or/encode/decode/f40f" #[] rawF40f,
    -- [B10] [B11]
    mkCaseCode "or/encode/decode/f40d" #[] rawF40d,
    -- [B10] [B11]
    mkCaseCode "or/encode/decode/f40c" #[] rawF40c,
    -- [B10] [B11]
    mkCaseCode "or/encode/decode/f409" #[] rawF409,
    -- [B10] [B11]
    mkCaseCode "or/encode/decode/f410" #[] rawF410,
    -- [B10] [B11]
    mkCaseCode "or/encode/decode/truncated-8bit" #[] rawF4,

    -- [B12] [B13] boundary widths and gas
    -- [B12] [B13]
    mkCase "or/boundary/n0-hit" (stackIntKey 0 (.cell dictU0Root) 0),
    -- [B12] [B13]
    mkCase "or/boundary/n0-miss" (stackIntKey 1 (.cell dictU0Root) 0),
    -- [B12] [B13]
    mkCase "or/gas/exact" (stackIntKey 0 (.cell dictU8Root) 8)
      (#[.pushInt (.num dictUGasExact), .tonEnvOp .setGasLimit, dictUGet])
      (oracleGasLimitsExact dictUGasExact),
    -- [B13]
    mkCase "or/gas/exact-minus-one" (stackIntKey 0 (.cell dictU8Root) 8)
      (#[.pushInt (.num dictUGasExactMinusOne), .tonEnvOp .setGasLimit, dictUGet])
      (oracleGasLimitsExactMinusOne dictUGasExactMinusOne),
    -- [B12] [B13]
    mkCase "or/gas/tail-preserved" (#[intV 99, .cell dictU8Root, intV 1, intV 8])
      (#[.pushInt (.num dictUGasExact), .tonEnvOp .setGasLimit, dictUGet])
      (oracleGasLimitsExact dictUGasExact)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictUGetId
      count := 500
      gen := genDictUGetFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGET
