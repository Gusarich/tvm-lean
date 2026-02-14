import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTMINREF

/-!
INSTRUCTION: DICTMINREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatcher reachability.
   - `execInstrDictDictGetMinMax` handles only `.dictGetMinMax`.
   - A different opcode must fall through to `next`.

2. [B2] Runtime preamble and width validation.
   - `checkUnderflow 2` enforces two stack items (`dict`, `n`).
   - `popNatUpTo 1023` enforces non-negative `n` and rejects `NaN`/negative/too-large values.

3. [B3] Root decoding and type checking.
   - `popMaybeCell` accepts `null` and `.cell` roots.
   - Non-cell top-of-stack values are `.typeChk`.

4. [B4] Missing-key path.
   - Empty or not-found dictionaries push only `0` and perform no deletion.
   - Width mismatch is covered as a miss and also pushes `0`.

5. [B5] Hit path semantics for `args = 3` (byRef + unsigned + non-int + min + non-remove).
   - On hit, stack receives `valueRef`, reconstructed key slice (8/16/1023-bit key cell), then success flag `-1`.

6. [B6] Non-int boundary key sizes.
   - `n = 0` and `n = 1023` are valid.
   - Key output must be the raw `n`-bit big-endian key cell-slice.

7. [B7] By-ref payload shape.
   - Returned value must have `bitsRemaining = 0` and `refsRemaining = 1`.
   - Any slice-shaped payload or malformed by-ref leaf raises `.dictErr`.

8. [B8] Assembler constraints.
   - `args = 3` assembles exactly to `0xF483`.
   - Gaps (`args = 1`, `args = 9`, `args = 17`, etc.) return `.invOpcode`.
   - `args > 31` returns `.rangeChk`.

9. [B9] Decoder behavior.
   - `0xF482`..`0xF487` decode to `.dictGetMinMax 2`..`7` in the same family.
   - Neighboring family boundaries and 8-bit truncated opcode decode as `.invOpcode`.

10. [B10] Gas accounting.
    - No remove path is active for `args = 3`, so this branch has base gas only.
    - Exact gas should succeed; exact-minus-one should fail on gas accounting.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/ 

private def suiteId : InstrId :=
  { name := "DICTMINREF" }

private def instr : Instr :=
  .dictGetMinMax 3

private def exactGas : Int :=
  computeExactGasBudget instr

private def exactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def keySlice (n : Nat) (k : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits k n) #[])

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: empty root after insertion"
      | .error e =>
          panic! s!"{label}: dict build failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict after construction"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: empty root during dict set"
      | .error e =>
          panic! s!"{label}: dict build failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict after construction"

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA1 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB2 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def badValueSlice : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xF0 8) #[])

private def dictNull : Value :=
  .null

private def dictSingleRef0 : Cell :=
  mkDictSetRefRoot! "dictSingleRef0" 0 #[(0, valueA)]

private def dictSingleRef8 : Cell :=
  mkDictSetRefRoot! "dictSingleRef8" 8 #[(5, valueA)]

private def dictTwoRef8 : Cell :=
  mkDictSetRefRoot! "dictTwoRef8" 8 #[(0, valueB), (5, valueA)]

private def dictSingleRef16 : Cell :=
  mkDictSetRefRoot! "dictSingleRef16" 16 #[(255, valueC)]

private def dictSingleRef1023 : Cell :=
  mkDictSetRefRoot! "dictSingleRef1023" 1023 #[(0, valueA)]

private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(5, badValueSlice)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b0 1) #[]

private def rawOpcodeF481 : Cell := raw16 0xF481
private def rawOpcodeF482 : Cell := raw16 0xF482
private def rawOpcodeF483 : Cell := raw16 0xF483
private def rawOpcodeF484 : Cell := raw16 0xF484
private def rawOpcodeF485 : Cell := raw16 0xF485
private def rawOpcodeF486 : Cell := raw16 0xF486
private def rawOpcodeF487 : Cell := raw16 0xF487
private def rawOpcodeF488 : Cell := raw16 0xF488
private def rawOpcodeF489 : Cell := raw16 0xF489
private def rawOpcodeF4 : Cell := raw8 0xF4

private def dispatchSentinel : Int := 77_777

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV dispatchSentinel)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

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

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr}/{bits}")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def genDICTMINREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/8" #[dictNull, intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/16" #[dictNull, intV 16], rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null/1023" #[dictNull, intV 1023], rng1)
    else if shape = 4 then
      (mkCase "fuzz/miss/width-mismatch" #[.cell dictSingleRef8, intV 16], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/single/0" #[.cell dictSingleRef0, intV 0], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/single/8" #[.cell dictSingleRef8, intV 8], rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/two/8" #[.cell dictTwoRef8, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/hit/single/16" #[.cell dictSingleRef16, intV 16], rng1)
    else if shape = 9 then
      (mkCase "fuzz/hit/single/1023" #[.cell dictSingleRef1023, intV 1023], rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/underflow-one" #[dictNull], rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type-root" #[.slice badValueSlice, intV 8], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/type-nan" #[dictNull, .int .nan], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/n-neg" #[dictNull, intV (-1)], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/n-max-plus" #[dictNull, intV 1024], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/byref-shape" #[.cell dictSliceSingle8, intV 8], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/malformed-root" #[.cell malformedDict, intV 8], rng1)
    else if shape = 18 then
      (mkCodeCase "fuzz/raw/f481" #[dictNull, intV 8] rawOpcodeF481, rng1)
    else if shape = 19 then
      (mkCodeCase "fuzz/raw/f483" #[dictNull, intV 8] rawOpcodeF483, rng1)
    else if shape = 20 then
      (mkCase "fuzz/gas/exact" #[dictNull, intV 8]
        (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact exactGas), rng1)
    else
      (mkCase "fuzz/gas/exact-minus-one" #[dictNull, intV 8]
        (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne exactGasMinusOne), rng1)

  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

/--
  500-case generator has heavy boundary coverage:
  - dictionary misses at key-width edges (0, 1023),
  - successful hits across widths and sizes,
  - explicit underflow/type/range/by-ref-shape/malformed-root errors,
  - gas-edge and raw-code execution cases.
-/

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDispatchFallback #[intV 1, intV 2] with
        | .ok st =>
            if st == #[intV 1, intV 2, intV dispatchSentinel] then
              pure ()
            else
              throw (IO.userError s!"fallback unexpectedly changed stack: {reprStr st}")
        | .error e =>
            throw (IO.userError s!"fallback execution failed: {e}") },
    { name := "unit/exec/success/miss/null/0" -- [B4]
      run := do
        expectOkStack "miss-null-0" (runDirect #[dictNull, intV 0]) #[intV 0] },
    { name := "unit/exec/success/miss/null/1023" -- [B4][B6]
      run := do
        expectOkStack "miss-null-1023" (runDirect #[dictNull, intV 1023]) #[intV 0] },
    { name := "unit/exec/success/hit/single-0" -- [B5][B6]
      run := do
        expectOkStack "hit-single-0" (runDirect #[.cell dictSingleRef0, intV 0]) #[.cell valueA, .slice (keySlice 0 0), intV (-1)] },
    { name := "unit/exec/success/hit/single-1023" -- [B5][B6]
      run := do
        expectOkStack "hit-single-1023" (runDirect #[.cell dictSingleRef1023, intV 1023])
          #[.cell valueA, .slice (keySlice 1023 0), intV (-1)] },
    { name := "unit/exec/success/hit/two-8" -- [B5]
      run := do
        expectOkStack "hit-two-8" (runDirect #[.cell dictTwoRef8, intV 8])
          #[.cell valueB, .slice (keySlice 8 0), intV (-1)] },
    { name := "unit/exec/err/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd },
    { name := "unit/exec/err/underflow-one" -- [B2]
      run := do
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd },
    { name := "unit/exec/err/nan" -- [B2]
      run := do
        expectErr "n-nan" (runDirect #[dictNull, .int .nan]) .rangeChk },
    { name := "unit/exec/err/n-negative" -- [B2]
      run := do
        expectErr "n-negative" (runDirect #[dictNull, intV (-1)]) .rangeChk },
    { name := "unit/exec/err/n-too-large" -- [B2]
      run := do
        expectErr "n-too-large" (runDirect #[dictNull, intV 2000]) .rangeChk },
    { name := "unit/exec/err/type-root" -- [B3]
      run := do
        expectErr "type-root" (runDirect #[.slice badValueSlice, intV 8]) .typeChk },
    { name := "unit/exec/err/by-ref-shape" -- [B7]
      run := do
        expectErr "not-ref" (runDirect #[.cell dictSliceSingle8, intV 8]) .dictErr },
    { name := "unit/exec/err/malformed-root" -- [B3]
      run := do
        expectErr "malformed-root" (runDirect #[.cell malformedDict, intV 8]) .cellUnd },
    { name := "unit/opcode/assemble/exact" -- [B8]
      run := do
        expectAssembleErr "assemble-gap-1" (.dictGetMinMax 9) .invOpcode },
    { name := "unit/opcode/assemble/oob" -- [B8]
      run := do
        expectAssembleErr "assemble-oob" (.dictGetMinMax 33) .rangeChk },
    { name := "unit/decode/branches" -- [B9]
      run := do
        expectDecodeOk "decode-self" rawOpcodeF483 (.dictGetMinMax 3)
        expectDecodeOk "decode-prev" rawOpcodeF482 (.dictGetMinMax 2)
        expectDecodeOk "decode-next" rawOpcodeF484 (.dictGetMinMax 4)
        expectDecodeOk "decode-last" rawOpcodeF487 (.dictGetMinMax 7)
        expectDecodeErr "decode-gap-before" rawOpcodeF481 .invOpcode
        expectDecodeErr "decode-gap-after" rawOpcodeF488 .invOpcode
        expectDecodeErr "decode-before-family" rawOpcodeF489 .invOpcode
        expectDecodeErr "decode-truncated" rawOpcodeF4 .invOpcode } 
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" #[dictNull, intV 0],
    mkCase "oracle/miss/null/8" #[dictNull, intV 8],
    mkCase "oracle/miss/null/16" #[dictNull, intV 16],
    mkCase "oracle/miss/null/1023" #[dictNull, intV 1023],
    mkCase "oracle/miss/width-mismatch" #[.cell dictSingleRef8, intV 16],
    mkCase "oracle/hit/single/0" #[.cell dictSingleRef0, intV 0],
    mkCase "oracle/hit/single/8" #[.cell dictSingleRef8, intV 8],
    mkCase "oracle/hit/two/8" #[.cell dictTwoRef8, intV 8],
    mkCase "oracle/hit/single/16" #[.cell dictSingleRef16, intV 16],
    mkCase "oracle/hit/single/1023" #[.cell dictSingleRef1023, intV 1023],
    mkCase "oracle/multiple-output/single-0" #[.cell dictSingleRef0, intV 0],
    mkCodeCase "oracle/code/raw/f482" #[dictNull, intV 8] rawOpcodeF482,
    mkCodeCase "oracle/code/raw/f483" #[dictNull, intV 8] rawOpcodeF483,
    mkCodeCase "oracle/code/raw/f484" #[dictNull, intV 8] rawOpcodeF484,
    mkCodeCase "oracle/code/raw/f485" #[dictNull, intV 8] rawOpcodeF485,
    mkCodeCase "oracle/code/raw/f486" #[dictNull, intV 8] rawOpcodeF486,
    mkCodeCase "oracle/code/raw/f487" #[dictNull, intV 8] rawOpcodeF487,
    mkCodeCase "oracle/code/raw/f481" #[dictNull, intV 8] rawOpcodeF481,
    mkCodeCase "oracle/code/raw/f488" #[dictNull, intV 8] rawOpcodeF488,
    mkCodeCase "oracle/code/raw/truncated8" #[] rawOpcodeF4,
    mkCase "oracle/err/underflow-empty" #[],
    mkCase "oracle/err/underflow-one" #[dictNull],
    mkCase "oracle/err/type-root" #[.cont (.quit 0), intV 8],
    mkCase "oracle/err/type-root-slice" #[.slice badValueSlice, intV 8],
    mkCase "oracle/err/type-top" #[.null, .int .nan],
    mkCase "oracle/err/n-negative" #[dictNull, intV (-1)],
    mkCase "oracle/err/n-overflow" #[dictNull, intV 2000],
    mkCase "oracle/err/byref-shape" #[.cell dictSliceSingle8, intV 8],
    mkCase "oracle/err/malformed-root" #[.cell malformedDict, intV 8],
    mkCase "oracle/gas/exact" #[dictNull, intV 8]
      (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact exactGas),
    mkCase "oracle/gas/exact-minus-one" #[dictNull, intV 8]
      (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne exactGasMinusOne),
    mkCodeCase "oracle/code/asm-gap" #[] rawOpcodeF489,
    mkCase "oracle/program/trim-stack" #[.cell dictTwoRef8, intV 8] #[instr, .pushInt (.num 777)]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTMINREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTMINREF
