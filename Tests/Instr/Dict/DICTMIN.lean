import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTMIN

/-!
INSTRUCTION: DICTMIN

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch branch.
   - `execInstrDictDictGetMinMax` handles only `.dictGetMinMax`; other opcodes must follow `next`.

2. [B2] Runtime precondition and `n` validation.
   - `checkUnderflow 2` runs first.
   - `popNatUpTo 1023` rejects non-int `.typeChk`, `.nan`, negative, and values `> 1023`.

3. [B3] Dictionary root handling.
   - `popMaybeCell` accepts only `.null` and `.cell`.
   - Any other root type raises `.typeChk`.

4. [B4] Miss behavior.
   - `null` or empty traversal misses return a single `0`.

5. [B5] Hit behavior.
   - Valid non-empty hit returns value slice, reconstructed key slice (exactly `n` bits), and `-1`.

6. [B6] Key width boundaries.
   - `n = 0` produces empty key slice.
   - Small and max-width requests (`n = 1`, `2`, `16`, `1023`) keep prefix behavior deterministic and match traversal order.

7. [B7] By-ref retrieval (`args5 = 3`).
   - Acceptable value shape is exactly `bits=0` and `refs=1`, producing `.cell`.
   - Malformed value shapes raise `.dictErr`.

8. [B8] Assembler/decoder behavior.
   - `.dictGetMinMax 2` must encode to `0xF482` and `.dictGetMinMax 3` to `0xF483`.
   - Same-family opcodes (`0xF48A..0xF48F`, `0xF492..0xF497`, `0xF49A..0xF49F`) must decode.
   - Gaps and truncated streams (e.g. `0xF488`, `0xF489`, `0xF4`) must fail with `.invOpcode`.

9. [B9] Gas accounting.
   - This variant does not set `remove`, so base gas only.
   - Exact gas should pass and exact-minus-one should fail.

10. [B10] Malformed traversals.
   - Invalid root shapes can produce `.cellUnd` / `.dictErr` depending on the corruption.

TOTAL BRANCHES: 10

Each oracle test below is tagged with the branches it targets.
-/

private def dictMinId : InstrId :=
  { name := "DICTMIN" }

private def dictMin : Instr :=
  .dictGetMinMax 2

private def dictMinRef : Instr :=
  .dictGetMinMax 3

private def mkSliceFromNat (w : Nat) (n : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w n) #[])

private def valueA : Slice :=
  mkSliceFromNat 0xA5 8

private def valueB : Slice :=
  mkSliceFromNat 0x5A 8

private def valueC : Slice :=
  mkSliceFromNat 0xC3 8

private def byRefCell : Cell :=
  Cell.mkOrdinary (natToBits 0xBEEF 16) #[]

private def byRefGoodValue : Slice :=
  Slice.ofCell (Cell.mkOrdinary #[] #[byRefCell])

private def byRefBadBits : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[byRefCell])

private def byRefBadRefsZero : Slice :=
  Slice.ofCell (Cell.mkOrdinary #[] #[])

private def byRefBadRefsTwo : Slice :=
  Slice.ofCell (Cell.mkOrdinary #[] #[Cell.empty, Cell.empty])

private def mkDictFromPairs (label : String) (_n : Nat) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let (keyBits, value) := pair
      match root with
      | some c =>
          match dictSetSliceWithCells (some c) keyBits value .set with
          | .ok (some cNew, _, _, _) =>
              root := cNew
          | _ =>
              panic! s!"{label}: failed to extend dictionary"
      | none =>
          match dictSetSliceWithCells none keyBits value .set with
          | .ok (some cNew, _, _, _) =>
              root := cNew
          | _ =>
              panic! s!"{label}: failed to initialize dictionary"
    match root with
    | some r => r
          | none => panic! s!"{label}: dictionary is empty"

private def dict8Root : Cell :=
  mkDictFromPairs "dict8Root" 8 #[(natToBits 5 8, valueA), (natToBits 128 8, valueB), (natToBits 255 8, valueC)]

private def dict16Root : Cell :=
  mkDictFromPairs "dict16Root" 16 #[(natToBits 3 16, valueA), (natToBits 65535 16, valueC)]

private def dict1Root : Cell :=
  mkDictFromPairs "dict1Root" 1 #[(natToBits 0 1, valueA), (natToBits 1 1, valueB)]

private def dict0Root : Cell :=
  mkDictFromPairs "dict0Root" 0 #[(natToBits 0 0, valueA)]

private def dictByRefGoodRoot : Cell :=
  mkDictFromPairs "dictByRefGoodRoot" 8 #[(natToBits 1 8, byRefGoodValue)]

private def dictByRefBadBitsRoot : Cell :=
  mkDictFromPairs "dictByRefBadBitsRoot" 8 #[(natToBits 1 8, byRefBadBits)]

private def dictByRefBadRefsRoot : Cell :=
  mkDictFromPairs "dictByRefBadRefsRoot" 8 #[(natToBits 1 8, byRefBadRefsTwo)]

private def malformedDictCellBits : Cell :=
  Cell.mkOrdinary (natToBits 0 2) #[]

private def malformedDictCellRefs : Cell :=
  Cell.mkOrdinary (natToBits 0 2) #[Cell.empty]

private def dictMinGas : Int :=
  computeExactGasBudget dictMin

private def dictMinGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictMin

private def gasExact : OracleGasLimits :=
  oracleGasLimitsExact dictMinGas

private def gasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictMinGasMinusOne

private def rawF482 : Cell :=
  Cell.mkOrdinary (natToBits 0xF482 16) #[]

private def rawF483 : Cell :=
  Cell.mkOrdinary (natToBits 0xF483 16) #[]

private def rawF48A : Cell :=
  Cell.mkOrdinary (natToBits 0xF48A 16) #[]

private def rawF48F : Cell :=
  Cell.mkOrdinary (natToBits 0xF48F 16) #[]

private def rawF488 : Cell :=
  Cell.mkOrdinary (natToBits 0xF488 16) #[]

private def rawF489 : Cell :=
  Cell.mkOrdinary (natToBits 0xF489 16) #[]

private def rawF4 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def fallbackSentinel : Int := 123_901

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictMin])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictMinId
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
    instr := dictMinId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk
    (label : String)
    (cell : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected exact decode, got {rest.bitsRemaining}b/{rest.refsRemaining}r")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {actual}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def runDictMinDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV fallbackSentinel)) stack

private def runDictMinDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax dictMin stack

private def runDictMinRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax dictMinRef stack

private def expectHitShape
    (label : String)
    (result : Except Excno (Array Value))
    (keyBits : Nat) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")
  | .ok #[.slice value, .slice key, .int (.num flag)] =>
      if flag != (-1 : Int) then
        throw (IO.userError s!"{label}: expected -1 flag, got {flag}")
      else if value.bitsRemaining != 8 then
        throw (IO.userError s!"{label}: expected value width 8, got {value.bitsRemaining}")
      else if key.bitsRemaining != keyBits then
        throw (IO.userError s!"{label}: expected key width {keyBits}, got {key.bitsRemaining}")
  | .ok st =>
      throw (IO.userError s!"{label}: expected [slice,slice,-1], got {reprStr st}")

private def expectPrefixedHitShape
    (label : String)
    (result : Except Excno (Array Value))
    (pfx : Int)
    (keyBits : Nat) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")
  | .ok #[.int (.num p), .slice value, .slice key, .int (.num flag)] =>
      if p != pfx then
        throw (IO.userError s!"{label}: expected prefix {pfx}, got {p}")
      else if flag != (-1 : Int) then
        throw (IO.userError s!"{label}: expected -1 flag, got {flag}")
      else if value.bitsRemaining != 8 then
        throw (IO.userError s!"{label}: expected value width 8, got {value.bitsRemaining}")
      else if key.bitsRemaining != keyBits then
        throw (IO.userError s!"{label}: expected key width {keyBits}, got {key.bitsRemaining}")
  | .ok st =>
      throw (IO.userError s!"{label}: expected [prefix,slice,slice,-1], got {reprStr st}")

private def genDictMinFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/ok/hit/n8" (#[(.cell dict8Root), intV 8])
    else if shape = 1 then
      mkCase "fuzz/ok/hit/n16" (#[(.cell dict16Root), intV 16])
    else if shape = 2 then
      mkCase "fuzz/ok/hit/n1" (#[(.cell dict1Root), intV 1])
    else if shape = 3 then
      mkCase "fuzz/ok/hit/n0" (#[(.cell dict0Root), intV 0])
    else if shape = 4 then
      mkCase "fuzz/ok/hit/preserve-prefix" (#[(.int (.num 77)), .cell dict8Root, intV 8])
    else if shape = 5 then
      mkCase "fuzz/ok/miss/null-0" (#[(.null), intV 0])
    else if shape = 6 then
      mkCase "fuzz/ok/miss/null-8" (#[(.null), intV 8])
    else if shape = 7 then
      mkCase "fuzz/ok/miss/null-1023" (#[(.null), intV 1023])
    else if shape = 8 then
      mkCase "fuzz/ok/byref/hit" (#[(.cell dictByRefGoodRoot), intV 8]) (program := #[dictMinRef])
    else if shape = 9 then
      mkCase "fuzz/ok/byref/malformed-bits" (#[(.cell dictByRefBadBitsRoot), intV 8]) (program := #[dictMinRef])
    else if shape = 10 then
      mkCase "fuzz/ok/byref/malformed-refs" (#[(.cell dictByRefBadRefsRoot), intV 8]) (program := #[dictMinRef])
    else if shape = 11 then
      mkCase "fuzz/err/underflow-empty" #[]
    else if shape = 12 then
      mkCase "fuzz/err/underflow-one" (#[(.null)])
    else if shape = 13 then
      mkCase "fuzz/err/type-n-null" (#[(.cell dict8Root), .null])
    else if shape = 14 then
      mkCase "fuzz/err/type-n-nan" (#[(.cell dict8Root), .int .nan])
    else if shape = 15 then
      mkCase "fuzz/err/type-n-negative" (#[(.cell dict8Root), intV (-1)])
    else if shape = 16 then
      mkCase "fuzz/err/type-n-overflow" (#[(.cell dict8Root), intV 1024])
    else if shape = 17 then
      mkCase "fuzz/err/root-type" (#[(.builder Builder.empty), intV 8])
    else if shape = 18 then
      mkCase "fuzz/err/root-malformed-bits" (#[(.cell malformedDictCellBits), intV 8])
    else if shape = 19 then
      mkCase "fuzz/err/root-malformed-refs" (#[(.cell malformedDictCellRefs), intV 8])
    else if shape = 20 then
      mkCaseCode "fuzz/raw/f482" (#[] ) rawF482
    else if shape = 21 then
      mkCaseCode "fuzz/raw/f483" (#[] ) rawF483
    else if shape = 22 then
      mkCaseCode "fuzz/raw/f48a" (#[] ) rawF48A
    else if shape = 23 then
      mkCaseCode "fuzz/raw/f48f" (#[] ) rawF48F
    else if shape = 24 then
      mkCaseCode "fuzz/raw/f488" (#[] ) rawF488
    else if shape = 25 then
      mkCaseCode "fuzz/raw/f489" (#[] ) rawF489
    else if shape = 26 then
      mkCaseCode "fuzz/raw/f4-truncated" (#[] ) rawF4
    else if shape = 27 then
      mkCase "fuzz/gas/exact"
        (#[(.null), intV 8])
        (program := #[.pushInt (.num dictMinGas), .tonEnvOp .setGasLimit, dictMin])
        gasExact
    else if shape = 28 then
      mkCase "fuzz/gas/exact-minus-one"
        (#[(.null), intV 8])
        (program := #[.pushInt (.num dictMinGasMinusOne), .tonEnvOp .setGasLimit, dictMin])
        gasExactMinusOne
    else
      mkCase "fuzz/ok/hit-preserve-prefix" (#[(.int (.num 77)), .cell dict1Root, intV 1])
  let (tag, rng2) := randNat rng1 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng2)


def suite : InstrSuite where
  id := dictMinId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback-empty"
          (runDictMinDispatchFallback #[])
          #[.int (.num fallbackSentinel)]
        expectOkStack "fallback-one"
          (runDictMinDispatchFallback #[.int (.num 1), intV 2])
          #[.int (.num 1), intV 2, .int (.num fallbackSentinel)] },
    { name := "unit/underflow-and-n-checks" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictMinDirect #[]) .stkUnd
        expectErr "underflow-one" (runDictMinDirect #[.null]) .stkUnd
        expectErr "n-not-int" (runDictMinDirect #[.cell dict8Root, .null]) .typeChk
        expectErr "n-nan" (runDictMinDirect #[.cell dict8Root, .int .nan]) .rangeChk
        expectErr "n-negative" (runDictMinDirect #[.cell dict8Root, intV (-1)]) .rangeChk
        expectErr "n-overflow" (runDictMinDirect #[.cell dict8Root, intV 1024]) .rangeChk },
    { name := "unit/root-type" -- [B3]
      run := do
        expectErr "root-builder" (runDictMinDirect #[.builder Builder.empty, intV 8]) .typeChk
        expectErr "root-tuple" (runDictMinDirect #[.tuple #[], intV 8]) .typeChk
        expectErr "root-cont" (runDictMinDirect #[.cont (.quit 0), intV 8]) .typeChk },
    { name := "unit/miss-hit-key-boundaries" -- [B4][B5][B6]
      run := do
        expectOkStack "miss-null-0" (runDictMinDirect #[.null, intV 0]) #[intV 0]
        expectOkStack "miss-null-8" (runDictMinDirect #[.null, intV 8]) #[intV 0]
        expectHitShape "hit-n8" (runDictMinDirect #[.cell dict8Root, intV 8]) 8
        expectHitShape "hit-n16" (runDictMinDirect #[.cell dict16Root, intV 16]) 16
        expectHitShape "hit-n1" (runDictMinDirect #[.cell dict1Root, intV 1]) 1
        expectHitShape "hit-n0" (runDictMinDirect #[.cell dict0Root, intV 0]) 0
        expectPrefixedHitShape "preserve-prefix-hit"
          (runDictMinDirect #[.int (.num 77), .cell dict8Root, intV 8])
          77
          8 },
    { name := "unit/byref" -- [B7]
      run := do
        expectOkStack "byref-hit" (runDictMinRefDirect #[.cell dictByRefGoodRoot, intV 8])
          #[.cell byRefCell, .slice (mkSliceFromNat 1 8), intV (-1)]
        expectErr "byref-bad-bits" (runDictMinRefDirect #[.cell dictByRefBadBitsRoot, intV 8]) .dictErr
        expectErr "byref-bad-refs" (runDictMinRefDirect #[.cell dictByRefBadRefsRoot, intV 8]) .dictErr },
    { name := "unit/asm-decode" -- [B8]
      run := do
        match assembleCp0 [dictMin] with
        | .ok c =>
            if c.bits != natToBits 0xF482 16 then
              throw (IO.userError "DICTMIN encode mismatch")
        | .error e =>
            throw (IO.userError s!"assemble DICTMIN failed: {e}")
        match assembleCp0 [dictMinRef] with
        | .ok c =>
            if c.bits != natToBits 0xF483 16 then
              throw (IO.userError "DICTMINREF encode mismatch")
        | .error e =>
            throw (IO.userError s!"assemble DICTMINREF failed: {e}")
        expectDecodeOk "decode/f482" rawF482 (.dictGetMinMax 2)
        expectDecodeOk "decode/f483" rawF483 (.dictGetMinMax 3)
        expectDecodeOk "decode/f48a" rawF48A (.dictGetMinMax 10)
        expectDecodeOk "decode/f48f" rawF48F (.dictGetMinMax 15)
        expectDecodeErr "decode/f488" rawF488 .invOpcode
        expectDecodeErr "decode/f489" rawF489 .invOpcode
        expectDecodeErr "decode/truncated" rawF4 .invOpcode },
    { name := "unit/malformed" -- [B10]
      run := do
        expectErr "malformed-bits" (runDictMinDirect #[.cell malformedDictCellBits, intV 8]) .dictErr
        expectErr "malformed-refs" (runDictMinDirect #[.cell malformedDictCellRefs, intV 8]) .dictErr }
  ]
  oracle := #[
    -- [B1]
    mkCase "fallback/empty" #[],
    mkCase "fallback/one" #[.int (.num 1)],

    -- [B2]
    mkCase "err/underflow-empty" #[],
    mkCase "err/underflow-one" #[.null],
    mkCase "err/type-n-null" #[.cell dict8Root, .null],
    mkCase "err/type-n-nan" #[.cell dict8Root, .int .nan],
    mkCase "err/type-n-negative" #[.cell dict8Root, intV (-1)],
    mkCase "err/type-n-overflow" #[.cell dict8Root, intV 1024],

    -- [B3]
    mkCase "err/root-builder" #[.builder Builder.empty, intV 8],
    mkCase "err/root-tuple" #[.tuple #[], intV 8],
    mkCase "err/root-cont" #[.cont (.quit 0), intV 8],

    -- [B4]
    mkCase "miss/null-0" #[.null, intV 0],
    mkCase "miss/null-1" #[.null, intV 1],
    mkCase "miss/null-8" #[.null, intV 8],
    mkCase "miss/null-16" #[.null, intV 16],
    mkCase "miss/null-255" #[.null, intV 255],
    mkCase "miss/null-1023" #[.null, intV 1023],
    mkCase "miss/preserve-prefix" #[.int (.num 77), .null, intV 8],

    -- [B5][B6]
    mkCase "hit/n8" #[.cell dict8Root, intV 8],
    mkCase "hit/n8-pref" #[.int (.num 77), .cell dict8Root, intV 8],
    mkCase "hit/n16" #[.cell dict16Root, intV 16],
    mkCase "hit/n1" #[.cell dict1Root, intV 1],
    mkCase "hit/n0" #[.cell dict0Root, intV 0],
    mkCase "hit/alternate-n16" #[.cell dict16Root, intV 1],
    mkCase "hit/alternate-n1023" #[.cell dict8Root, intV 1023],

    -- [B7]
    mkCase "byref/hit" #[.cell dictByRefGoodRoot, intV 8] (#[dictMinRef]),
    mkCase "byref/bad-bits" #[.cell dictByRefBadBitsRoot, intV 8] (#[dictMinRef]),
    mkCase "byref/bad-refs" #[.cell dictByRefBadRefsRoot, intV 8] (#[dictMinRef]),

    -- [B8]
    mkCaseCode "decode/f482" #[.cell dict8Root, intV 8] rawF482,
    mkCaseCode "decode/f483" #[.cell dict8Root, intV 8] rawF483,
    mkCaseCode "decode/f48a" #[.cell dict8Root, intV 8] rawF48A,
    mkCaseCode "decode/f48f" #[.cell dict8Root, intV 8] rawF48F,
    mkCaseCode "decode/f488-gap" #[] rawF488,
    mkCaseCode "decode/f489-gap" #[] rawF489,
    mkCaseCode "decode/f4" #[] rawF4,

    -- [B9]
    mkCase "gas/exact" #[.cell dict8Root, intV 8]
      (#[.pushInt (.num dictMinGas), .tonEnvOp .setGasLimit, dictMin])
      gasExact,
    mkCase "gas/exact-minus-one" #[.cell dict8Root, intV 8]
      (#[.pushInt (.num dictMinGasMinusOne), .tonEnvOp .setGasLimit, dictMin])
      gasExactMinusOne,

    -- [B10]
    mkCase "malformed/bits" #[.cell malformedDictCellBits, intV 8],
    mkCase "malformed/refs" #[.cell malformedDictCellRefs, intV 8],
    mkCase "malformed/preserve-prefix" #[.int (.num 77), .cell malformedDictCellBits, intV 8]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictMinId
      count := 500
      gen := genDictMinFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTMIN
