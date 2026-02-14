import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGET

/-!
DICTIGET branch map (Lean + C++ reference):
- Lean sources read:
  - `TvmLean/Semantics/Exec/Dict/DictGet.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
  - `TvmLean/Semantics/VM/Ops/Cells.lean`
- C++ source read:
  - `/Users/daniil/Coding/ton/crypto/vm/dictops.cpp` (`exec_dict_get`).

1. [Dispatch] – instruction dispatch and non-matching fallback.
2. [Runtime guard] – underflow check (`checkUnderflow 3`) before any pops.
3. [n operand errors] – `n` type checks and range checks (`popNatUpTo 1023`):
   - `.typeChk` for non-int
   - `.rangeChk` for NaN/negative/>1023
4. [Root type errors] – `dictCell?` accepts only `null` or `cell`, otherwise `.typeChk`.
5. [Key parsing errors] – `popIntFinite` on key:
   - `.typeChk` for non-int
   - `.intOv` for NaN
6. [Key conversion] – out-of-range integer key (`dictKeyBits? = none`) is an immediate miss:
   - push `0` without dictionary traversal.
7. [Dictionary traversal/miss-hit] – with in-range key:
   - miss or `null` root => push `0`
   - hit => push value slice and `-1`
8. [By-ref retrieval] – `.dictGet int false true` requires matched value slice with
   exactly zero bits and one reference:
   - malformed payload => `.dictErr`
9. [Malformed roots] – invalid dictionary traversal root => `.dictErr`.
10. [Assembler/decoder] – valid encodings, invalid combinations (`.dictGet false true true`),
   and adjacent opcode boundaries in `0xf40a..0xf40f`.
11. [Gas accounting] – base gas only; check exact and exact-minus-one boundaries.

TOTAL BRANCHES: 11
-/

private def dictIGetId : InstrId := { name := "DICTIGET" }

private def dictIGetInstr : Instr := .dictGet true false false
private def dictIGetInstrRef : Instr := .dictGet true false true
private def dictIGetInstrUnsigned : Instr := .dictGet true true false

private def markerSlice (marker : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits marker 16) #[])

private def dict8Marker5 : Slice := markerSlice 0x51
private def dict8Marker6 : Slice := markerSlice 0x52
private def dict8MarkerN1 : Slice := markerSlice 0x53
private def dict1Marker0 : Slice := markerSlice 0x61
private def dict0Marker0 : Slice := markerSlice 0x62

private def byRefValueCell : Cell := Cell.mkOrdinary (natToBits 0x77 16) #[]
private def byRefLeaf : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[byRefValueCell])
private def byRefMalformedLeaf : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[])
private def byRefValueMarker : Value := .cell byRefValueCell

private def requireBits (label : String) (key : Int) (n : Nat) : BitString :=
  match dictKeyBits? key n false with
  | some bits => bits
  | none => panic! s!"{label}: unsupported key {key} for n={n}"

private def mkDictFromPairs (label : String) (n : Nat) (pairs : Array (Int × Nat)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        match st with
        | some root =>
            let k := pair.1
            let marker := pair.2
            match dictSetSliceWithCells (some root) (requireBits label k n) (markerSlice marker) .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            let k := pair.1
            let marker := pair.2
            match dictSetSliceWithCells none (requireBits label k n) (markerSlice marker) .set with
            | .ok (some root, _, _, _) => some root
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build dict"

private def mkDictFromPairsWithSlices (label : String) (n : Nat) (pairs : Array (Int × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        match st with
        | some root =>
            let k := pair.1
            let value := pair.2
            match dictSetSliceWithCells (some root) (requireBits label k n) value .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            let k := pair.1
            let value := pair.2
            match dictSetSliceWithCells none (requireBits label k n) value .set with
            | .ok (some root, _, _, _) => some root
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build dict"

private def dictN8Root : Cell :=
  mkDictFromPairs "dictN8Root" 8 #[(5, 0x51), (6, 0x52), (-1, 0x53)]

private def dictN1Root : Cell :=
  mkDictFromPairs "dictN1Root" 1 #[(0, 0x61)]

private def dictN0Root : Cell :=
  mkDictFromPairs "dictN0Root" 0 #[(0, 0x62)]

private def dictN8ByRefRoot : Cell :=
  mkDictFromPairsWithSlices
    "dictN8ByRefRoot"
    8
    #[(5, byRefLeaf), (6, markerSlice 0x58), (1, byRefMalformedLeaf)]

-- Minimal malformed root: valid label prefix with no refs and non-leaf constraints.
private def malformedDictCell : Cell := Cell.mkOrdinary (natToBits 0 2) #[]

private def dictIGetGasExact : Int := computeExactGasBudget dictIGetInstr
private def dictIGetGasExactMinusOne : Int := computeExactGasBudgetMinusOne dictIGetInstr

private def gasExact : OracleGasLimits := oracleGasLimitsExact dictIGetGasExact
private def gasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictIGetGasExact

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictIGetInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIGetId
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
    instr := dictIGetId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictIGetDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGet dictIGetInstr stack

private def runDictIGetDirectRef (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGet dictIGetInstrRef stack

private def runDictIGetDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGet instr (VM.push (intV 12345)) stack

private def opcodeSlice16 (w : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w 16) #[])

private def expectDecodeInvOpcode (label : String) (w : Nat) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 w) with
  | .ok (_, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, decode succeeded")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, got {reprStr e}")

private def genDictIGetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (tag, rng2) := randNat rng1 0 999_999
  let mkTag := s!"fuzz/{tag}/{shape}"
  let case0 :=
    if shape = 0 then
      mkCase (s!"{mkTag}/hit/key-5") (#[.cell dictN8Root, intV 5, intV 8])
    else if shape = 1 then
      mkCase (s!"{mkTag}/hit/key-neg1") (#[.cell dictN8Root, intV (-1), intV 8])
    else if shape = 2 then
      mkCase (s!"{mkTag}/miss-key-absent") (#[.cell dictN8Root, intV 7, intV 8])
    else if shape = 3 then
      mkCase (s!"{mkTag}/none-root-miss") (#[.null, intV 5, intV 8])
    else if shape = 4 then
      mkCase (s!"{mkTag}/key-range-pos") (#[.cell dictN8Root, intV 128, intV 8])
    else if shape = 5 then
      mkCase (s!"{mkTag}/key-range-neg") (#[.cell dictN8Root, intV (-129), intV 8])
    else if shape = 6 then
      mkCase (s!"{mkTag}/n-boundary-max") (#[.cell dictN8Root, intV 0, intV 1023])
    else if shape = 7 then
      mkCase (s!"{mkTag}/type-key-null") (#[.cell dictN8Root, .null, intV 8])
    else if shape = 8 then
      mkCase (s!"{mkTag}/type-dict-builder") (#[.builder Builder.empty, intV 5, intV 8])
    else if shape = 9 then
      mkCase (s!"{mkTag}/n-negative") (#[.cell dictN8Root, intV 5, intV (-1)])
    else if shape = 10 then
      mkCase (s!"{mkTag}/gas/base-exact-success") #[.null, intV 7, intV 8]
        (#[.pushInt (.num dictIGetGasExact), .tonEnvOp .setGasLimit, dictIGetInstr])
        gasExact
    else if shape = 11 then
      mkCase (s!"{mkTag}/gas/base-exact-minus-one") #[.null, intV 7, intV 8]
        (#[.pushInt (.num dictIGetGasExactMinusOne), .tonEnvOp .setGasLimit, dictIGetInstr])
        gasExactMinusOne
    else if shape = 12 then
      mkCase (s!"{mkTag}/byref-hit") (#[.cell dictN8ByRefRoot, intV 5, intV 8])
        (#[.dictGet true false true])
    else if shape = 13 then
      mkCase (s!"{mkTag}/byref-malformed") (#[.cell dictN8ByRefRoot, intV 1, intV 8])
        (#[.dictGet true false true])
    else
      mkCase (s!"{mkTag}/malformed-root") (#[.cell malformedDictCell, intV 5, intV 8])
  (case0, rng2)

def suite : InstrSuite where
  id := dictIGetId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        let sentinel : Int := 12_345
        expectOkStack
          "fallback/non-match"
          (runDictIGetDispatchFallback .add #[])
          #[intV sentinel]
        expectOkStack
          "match/executes-dictiget"
          (runDictIGetDirect #[.cell dictN8Root, intV 5, intV 8])
          #[.slice dict8Marker5, intV (-1)] },
    { name := "unit/underflow"
      run := do
        expectErr "empty-stack" (runDictIGetDirect #[]) .stkUnd
        expectErr "one-item" (runDictIGetDirect #[.int (.num 8)]) .stkUnd
        expectErr "two-items" (runDictIGetDirect #[.cell dictN8Root, intV 5]) .stkUnd },
    { name := "unit/n-operand-type-and-range"
      run := do
        expectErr "n-not-int" (runDictIGetDirect #[.cell dictN8Root, intV 5, .null]) .typeChk
        expectErr "n-nan" (runDictIGetDirect #[.cell dictN8Root, intV 5, .int .nan]) .rangeChk
        expectErr "n-negative" (runDictIGetDirect #[.cell dictN8Root, intV 5, intV (-1)]) .rangeChk
        expectErr "n-too-large" (runDictIGetDirect #[.cell dictN8Root, intV 5, intV 1024]) .rangeChk },
    { name := "unit/dict-type-and-key-type-checks"
      run := do
        expectErr "dict-not-null-or-cell" (runDictIGetDirect #[.builder Builder.empty, intV 5, intV 8]) .typeChk
        expectErr "key-not-int" (runDictIGetDirect #[.cell dictN8Root, .null, intV 8]) .typeChk
        expectErr "key-nan" (runDictIGetDirect #[.cell dictN8Root, .int .nan, intV 8]) .intOv
        expectErr "key-cell" (runDictIGetDirect #[.cell dictN8Root, .cell Cell.empty, intV 8]) .typeChk },
    { name := "unit/key-range-and-miss"
      run := do
        expectOkStack
          "out-of-range-positive"
          (runDictIGetDirect #[.cell dictN8Root, intV 128, intV 8])
          #[intV 0]
        expectOkStack
          "out-of-range-negative"
          (runDictIGetDirect #[.cell dictN8Root, intV (-129), intV 8])
          #[intV 0]
        expectOkStack
          "none-root"
          (runDictIGetDirect #[.null, intV 7, intV 8])
          #[intV 0]
        expectOkStack
          "miss-in-root"
          (runDictIGetDirect #[.cell dictN8Root, intV 7, intV 8])
          #[intV 0]
        expectOkStack
          "hit-n1"
          (runDictIGetDirect #[.cell dictN8Root, intV (-1), intV 8])
          #[.slice dict8MarkerN1, intV (-1)] },
    { name := "unit/stack-preserve"
      run := do
        expectOkStack
          "hit-preserve-prefix"
          (runDictIGetDirect #[intV 77, .cell dictN8Root, intV 5, intV 8])
          #[intV 77, .slice dict8Marker5, intV (-1)]
        expectOkStack
          "miss-preserve-prefix"
          (runDictIGetDirect #[intV 77, .null, intV 7, intV 8])
          #[intV 77, intV 0] },
    { name := "unit/n-zero-and-n-one"
      run := do
        expectOkStack
          "n0-hit"
          (runDictIGetDirect #[.cell dictN0Root, intV 0, intV 0])
          #[.slice dict0Marker0, intV (-1)]
        expectOkStack
          "n0-miss"
          (runDictIGetDirect #[.cell dictN0Root, intV 1, intV 0])
          #[intV 0]
        expectOkStack
          "n1-hit"
          (runDictIGetDirect #[.cell dictN1Root, intV 0, intV 1])
          #[.slice dict1Marker0, intV (-1)]
        expectOkStack
          "n1-miss"
          (runDictIGetDirect #[.cell dictN1Root, intV 1, intV 1])
          #[intV 0] },
    { name := "unit/asm-decode-paths"
      run := do
        match encodeCp0 (.dictGet true false false) with
        | .ok c =>
            if c != natToBits 0xf40a 16 then
              throw (IO.userError s!"encode/dictiget expected 0xf40a, got size {c.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictiget expected success, got {e}")
        match encodeCp0 (.dictGet true false true) with
        | .ok c =>
            if c != natToBits 0xf40b 16 then
              throw (IO.userError s!"encode/dictigetref expected 0xf40b, got size {c.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictigetref expected success, got {e}")
        match encodeCp0 (.dictGet true true false) with
        | .ok c =>
            if c != natToBits 0xf40e 16 then
              throw (IO.userError s!"encode/dictiget unsigned expected 0xf40e, got size {c.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictiget unsigned expected success, got {e}")
        match encodeCp0 (.dictGet false true false) with
        | .ok _ =>
            throw (IO.userError "encode/dictiget non-int key with unsigned should be invalid")
        | .error .invOpcode =>
            pure ()
        | .error e =>
            throw (IO.userError s!"encode invalid flags expected invOpcode, got {e}") },
    { name := "unit/decode-paths"
      run := do
        let s0 := opcodeSlice16 0xf40a
        let _ ← expectDecodeStep "decode/dictiget" s0 (.dictGet true false false) 16
        let s1 := opcodeSlice16 0xf40f
        let _ ← expectDecodeStep "decode/dictiget-refbyref" s1 (.dictGet true true true) 16
        expectDecodeInvOpcode "decode/invalid-gap" 0xf410
        let s2 := opcodeSlice16 0xf40e
        let _ ← expectDecodeStep "decode/dictiget-unsigned" s2 (.dictGet true true false) 16 },
    { name := "unit/by-ref-retrieval"
      run := do
        expectOkStack
          "ref-hit"
          (runDictIGetDirectRef #[.cell dictN8ByRefRoot, intV 5, intV 8])
          #[byRefValueMarker, intV (-1)]
        expectErr
          "ref-malformed-value"
          (runDictIGetDirectRef #[.cell dictN8ByRefRoot, intV 1, intV 8])
          .dictErr },
    { name := "unit/malformed-root"
      run := do
        expectErr
          "malformed-root"
          (runDictIGetDirect #[.cell malformedDictCell, intV 0, intV 8])
          .dictErr
        expectErr
          "malformed-root-with-tail"
          (runDictIGetDirect #[intV 77, .cell malformedDictCell, intV 0, intV 8])
          .dictErr }
  ]
  oracle := #[
    -- [B1] Dispatch/fallback.
    mkCase "fallback/empty-stack" #[],
    mkCase "fallback/one-operand" #[intV 8],

    -- [B3] `n` errors.
    mkCase "type/n-null" #[.cell dictN8Root, intV 5, .null],
    mkCase "type/n-builder" #[.cell dictN8Root, intV 5, .builder Builder.empty],
    mkCase "type/n-nan" #[.cell dictN8Root, intV 5, .int .nan],
    mkCase "range/n-negative" #[.cell dictN8Root, intV 5, intV (-1)],
    mkCase "range/n-too-large" #[.cell dictN8Root, intV 5, intV 1024],
    mkCase "range/n-max" #[.cell dictN8Root, intV 5, intV 1023],

    -- [B4] dictionary source type errors.
    mkCase "type/dict-builder" #[.builder Builder.empty, intV 5, intV 8],
    mkCase "type/dict-bool" (#[.tuple #[], intV 5, intV 8]),

    -- [B5] key type/range checks.
    mkCase "type/key-null" #[.cell dictN8Root, .null, intV 8],
    mkCase "type/key-cell" #[.cell dictN8Root, .cell Cell.empty, intV 8],
    mkCase "type/key-slice" #[.cell dictN8Root, .slice (Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[])), intV 8],
    mkCase "type/key-nan" #[.cell dictN8Root, .int .nan, intV 8],

    -- [B6] key-bit conversion misses.
    mkCase "conversion/out-of-range-positive" #[.cell dictN8Root, intV 128, intV 8],
    mkCase "conversion/out-of-range-negative" #[.cell dictN8Root, intV (-129), intV 8],
    mkCase "conversion/out-of-range-n1-positive" #[.cell dictN1Root, intV 1, intV 1],
    mkCase "conversion/out-of-range-n1-negative" #[.cell dictN1Root, intV (-2), intV 1],
    mkCase "conversion/out-of-range-n0-positive" #[.cell dictN0Root, intV 1, intV 0],

    -- [B7] miss/no-root branches.
    mkCase "lookup/none-root" #[.null, intV 7, intV 8],
    mkCase "lookup/none-root-tail" #[intV 77, .null, intV 7, intV 8],
    mkCase "lookup/miss-key-7" #[.cell dictN8Root, intV 7, intV 8],
    mkCase "lookup/miss-key-large" #[.cell dictN8Root, intV 127, intV 8],
    mkCase "lookup/miss-narrow" #[.cell dictN8Root, intV 9, intV 4],

    -- [B7][B8] hit branches with different widths.
    mkCase "lookup/hit-key-5" #[.cell dictN8Root, intV 5, intV 8],
    mkCase "lookup/hit-key-6" #[.cell dictN8Root, intV 6, intV 8],
    mkCase "lookup/hit-key-neg1" #[.cell dictN8Root, intV (-1), intV 8],
    mkCase "lookup/hit-tail-preserved" #[intV 17, .cell dictN8Root, intV 5, intV 8],
    mkCase "lookup/hit-n1-key-0" #[.cell dictN1Root, intV 0, intV 1],
    mkCase "lookup/hit-n0-key-0" #[.cell dictN0Root, intV 0, intV 0],

    -- [B9] malformed dict payload.
    mkCase "error/malformed-root" #[.cell malformedDictCell, intV 5, intV 8],
    mkCase "error/malformed-root-tail" #[intV 99, .cell malformedDictCell, intV 0, intV 8],

    -- [B8] by-ref path (success + malformed).
    mkCase "byref/hit" (#[.cell dictN8ByRefRoot, intV 5, intV 8]) #[.dictGet true false true],
    mkCase "byref/malformed-value" (#[.cell dictN8ByRefRoot, intV 1, intV 8]) #[.dictGet true false true],

    -- [B11] gas exact and near-exact checks.
    mkCase "gas/exact-base" #[.null, intV 7, intV 8]
      (#[.pushInt (.num dictIGetGasExact), .tonEnvOp .setGasLimit, dictIGetInstr])
      gasExact,
    mkCase "gas/exact-minus-one" #[.null, intV 7, intV 8]
      (#[.pushInt (.num dictIGetGasExactMinusOne), .tonEnvOp .setGasLimit, dictIGetInstr])
      gasExactMinusOne,
    mkCase "gas/exact-tail" #[intV 77, .cell dictN8Root, intV 5, intV 8]
      (#[.pushInt (.num dictIGetGasExact), .tonEnvOp .setGasLimit, dictIGetInstr])
      gasExact,

    -- Assembly/decode corner cases via raw opcode fixtures.
    mkCaseCode "raw/decode/fallback-0xf410" #[] (Cell.mkOrdinary (natToBits 0xf410 16) #[]),
    mkCaseCode "raw/decode/f40f" #[] (Cell.mkOrdinary (natToBits 0xf40f 16) #[]),
    mkCaseCode "raw/decode/invalid-short" #[] (Cell.mkOrdinary (natToBits 0xf4 8) #[])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictIGetId
      count := 500
      gen := genDictIGetFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGET
