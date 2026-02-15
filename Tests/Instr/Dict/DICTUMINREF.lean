import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTUMINREF

/-!
INSTRUCTION: DICTUMINREF

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch branch.
   `execInstrDictDictGetMinMax` must route `.dictGetMinMax` only; unrelated instructions
   must call `next`.

2. [B2] Runtime preamble and width checks.
   `checkUnderflow 2` requires dictionary and `n`.
   `popNatUpTo` with `maxN = 256` rejects non-natural, `NaN`, negative, and values above `256`.
   Width errors use `.rangeChk`.

3. [B3] Root typing.
   `popMaybeCell` accepts only `null` and `cell` roots; all other value kinds produce
   `.typeChk` before dictionary traversal.

4. [B4] Empty/miss behavior.
   `dictMinMaxWithCells` returning `none` pushes only `0` (no key/value, root unchanged
   because remove flag is clear).

5. [B5] Hit behavior (unsigned-by-ref no-remove path).
   For `.dictGetMinMax 7`, `fetchMin` (`invertFirst = false`) returns the minimum key entry,
   converts key bits with `bitsToNat`, pushes value as `.cell`, key as unsigned `Int`, and
   success flag `-1`.

6. [B6] Boundary widths and ordering.
   Valid widths include `0`, `1`, `8`, `16`, and `256`.
   Width errors at `257` and above are covered under [B2].

7. [B7] By-ref payload structural validation.
   Found value must be a slice of zero bits with exactly one ref.
   Any other shape triggers `.dictErr`.

8. [B8] Assembler behavior.
   `.dictGetMinMax 7` is valid and assembles to `0xF487`.
   In-range unsupported values and out-of-family values map to `.invOpcode`.
   Values above `31` return `.rangeChk`.

9. [B9] Decoder behavior.
   Family `0xF482..0xF487` decodes to `.dictGetMinMax 2..7`.
   `0xF488`, `0xF489`, and truncated `0xF4` are decode errors.

10. [B10] Gas accounting.
    Non-remove by-ref variant has fixed base gas in this repository (no dynamic
    `cellCreateGasPrice` penalty).
    Exact-gas oracle should succeed, exact-minus-one should fail.

11. [B11] Structural dictionary faults.
    Malformed roots can raise `.cellUnd`/`.dictErr` depending on how traversal fails.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn].
-/

private def dictUMinRefId : InstrId :=
  { name := "DICTUMINREF" }

private def dictUMinRefInstr : Instr :=
  .dictGetMinMax 7

private def dictUMinRefExactGas : Int :=
  computeExactGasBudget dictUMinRefInstr

private def dictUMinRefExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictUMinRefInstr

private def dictUMinRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictUMinRefExactGas

private def dictUMinRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictUMinRefExactGasMinusOne

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def dispatchSentinel : Int :=
  88_909

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA1 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB2 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def byRefGood : Cell :=
  Cell.mkOrdinary #[] #[Cell.empty]

private def byRefBadBits : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[Cell.empty]

private def byRefBadNoRefs : Cell :=
  Cell.mkOrdinary #[] #[]

private def byRefBadTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[Cell.empty, Cell.empty]

private def dictNull : Value :=
  .null

private def mkDictRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid unsigned key ({k}), n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root after inserting ({k}), n={n}"
      | .error e =>
          panic! s!"{label}: failed insert ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: dictionary construction produced empty root"

private def dictSingleRef0 : Cell :=
  mkDictRefRoot! "dictSingleRef0" 0 #[(0, valueA)]

private def dictSingleRef1 : Cell :=
  mkDictRefRoot! "dictSingleRef1" 1 #[(1, valueA)]

private def dictSingleRef8 : Cell :=
  mkDictRefRoot! "dictSingleRef8" 8 #[(5, valueA)]

private def dictTwoRef8 : Cell :=
  mkDictRefRoot! "dictTwoRef8" 8 #[(5, valueA), (200, valueB)]

private def dictThreeRef8 : Cell :=
  mkDictRefRoot! "dictThreeRef8" 8 #[(1, valueA), (7, valueB), (250, valueC)]

private def dictSingleRef16 : Cell :=
  mkDictRefRoot! "dictSingleRef16" 16 #[(256, valueA)]

private def dictSingleRef256 : Cell :=
  mkDictRefRoot! "dictSingleRef256" 256 #[(0, valueA)]

private def dictTwoRef256 : Cell :=
  mkDictRefRoot! "dictTwoRef256" 256 #[(0, valueA), (255, valueB)]

private def dictByRefGood : Cell :=
  mkDictRefRoot! "dictByRefGood" 8 #[(5, byRefGood)]

private def dictByRefBadBits : Cell :=
  mkDictRefRoot! "dictByRefBadBits" 8 #[(5, byRefBadBits)]

private def dictByRefBadNoRefs : Cell :=
  mkDictRefRoot! "dictByRefBadNoRefs" 8 #[(5, byRefBadNoRefs)]

private def dictByRefBadTwoRefs : Cell :=
  mkDictRefRoot! "dictByRefBadTwoRefs" 8 #[(5, byRefBadTwoRefs)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1 1) #[]

private def rawOpcodeF482 : Cell := raw16 0xF482
private def rawOpcodeF483 : Cell := raw16 0xF483
private def rawOpcodeF484 : Cell := raw16 0xF484
private def rawOpcodeF485 : Cell := raw16 0xF485
private def rawOpcodeF486 : Cell := raw16 0xF486
private def rawOpcodeF487 : Cell := raw16 0xF487
private def rawOpcodeF488 : Cell := raw16 0xF488
private def rawOpcodeF489 : Cell := raw16 0xF489
private def rawOpcodeF4 : Cell := raw8 0xF4

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictUMinRefInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUMinRefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUMinRefId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictUMinRefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax (.add) (VM.push (intV dispatchSentinel)) stack

private def runDictUMinRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax dictUMinRefInstr stack

private def expectDecodeOk
    (label : String)
    (cell : Cell)
    (expected : Instr)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decoder did not consume full cell")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
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

private def genDICTUMINRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/1" #[dictNull, intV 1], rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/8" #[dictNull, intV 8], rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null/16" #[dictNull, intV 16], rng1)
    else if shape = 4 then
      (mkCase "fuzz/miss/null/256" #[dictNull, intV 256], rng1)
    else if shape = 5 then
      (mkCase "fuzz/miss/mismatch-width" #[.cell dictSingleRef8, intV 16], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/single/ref0" #[.cell dictSingleRef0, intV 0], rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/single/ref8" #[.cell dictSingleRef8, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/hit/two/ref8" #[.cell dictTwoRef8, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/hit/three/ref8" #[.cell dictThreeRef8, intV 8], rng1)
    else if shape = 10 then
      (mkCase "fuzz/hit/single/ref16" #[.cell dictSingleRef16, intV 16], rng1)
    else if shape = 11 then
      (mkCase "fuzz/hit/single/ref256" #[.cell dictSingleRef256, intV 256], rng1)
    else if shape = 12 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 13 then
      (mkCase "fuzz/underflow/one" #[intV 8], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/root-type-tuple" #[.tuple #[], intV 8], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/root-type-cont" #[.cont (.quit 0), intV 8], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/nan" #[.cell dictSingleRef8, .int .nan], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/n-negative" #[.cell dictSingleRef8, intV (-1)], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/n-too-large" #[.cell dictSingleRef8, intV 257], rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/malformed-root" #[.cell malformedDict, intV 8], rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/byref-bad-bits" #[.cell dictByRefBadBits, intV 8], rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/byref-bad-no-refs" #[.cell dictByRefBadNoRefs, intV 8], rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/byref-bad-two-refs" #[.cell dictByRefBadTwoRefs, intV 8], rng1)
    else if shape = 23 then
      (mkRawCase "fuzz/raw/f485" #[.cell dictSingleRef8, intV 8] rawOpcodeF485, rng1)
    else if shape = 24 then
      (mkRawCase "fuzz/raw/f487" #[.cell dictSingleRef8, intV 8] rawOpcodeF487, rng1)
    else if shape = 25 then
      (mkRawCase "fuzz/raw/f488" #[] rawOpcodeF488, rng1)
    else if shape = 26 then
      (mkRawCase "fuzz/raw/f489" #[] rawOpcodeF489, rng1)
    else if shape = 27 then
      (mkRawCase "fuzz/raw/f4" #[] rawOpcodeF4, rng1)
    else if shape = 28 then
      (mkCase "fuzz/gas/exact" #[dictNull, intV 8]
        (#[.pushInt (.num dictUMinRefExactGas), .tonEnvOp .setGasLimit, dictUMinRefInstr])
        dictUMinRefGasExact, rng1)
    else
      (mkCase "fuzz/gas/exact-minus-one" #[dictNull, intV 8]
        (#[.pushInt (.num dictUMinRefExactGasMinusOne), .tonEnvOp .setGasLimit, dictUMinRefInstr])
        dictUMinRefGasExactMinusOne, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr dictUMinRefId

def suite : InstrSuite where
  id := dictUMinRefId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDictUMinRefDispatchFallback #[.cell dictSingleRef8, intV 8] with
        | .ok st =>
            if st == #[.cell dictSingleRef8, intV 8, intV dispatchSentinel] then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback failed, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback failed with exception {e}")
    }
    ,
    { name := "unit/miss/null/0" -- [B2][B3][B4]
      run := do
        expectOkStack "miss-null-0" (runDictUMinRefDirect #[dictNull, intV 0]) #[intV 0]
    }
    ,
    { name := "unit/miss/null/8" -- [B2][B3][B4]
      run := do
        expectOkStack "miss-null-8" (runDictUMinRefDirect #[dictNull, intV 8]) #[intV 0]
    }
    ,
    { name := "unit/miss/null/16" -- [B2][B3][B4]
      run := do
        expectOkStack "miss-null-16" (runDictUMinRefDirect #[dictNull, intV 16]) #[intV 0]
    }
    ,
    { name := "unit/miss/null/256" -- [B2][B3][B4][B6]
      run := do
        expectOkStack "miss-null-256" (runDictUMinRefDirect #[dictNull, intV 256]) #[intV 0]
    }
    ,
    { name := "unit/hit/single/ref0" -- [B4][B5]
      run := do
        expectOkStack "hit-single-ref0"
          (runDictUMinRefDirect #[.cell dictSingleRef0, intV 0])
          #[.cell valueA, intV 0, intV (-1)]
    }
    ,
    { name := "unit/hit/single/ref8" -- [B4][B5]
      run := do
        expectOkStack "hit-single-ref8"
          (runDictUMinRefDirect #[.cell dictSingleRef8, intV 8])
          #[.cell valueA, intV 5, intV (-1)]
    }
    ,
    { name := "unit/hit/two/ref8" -- [B4][B5]
      run := do
        expectOkStack "hit-two-ref8"
          (runDictUMinRefDirect #[.cell dictTwoRef8, intV 8])
          #[.cell valueA, intV 5, intV (-1)]
    }
    ,
    { name := "unit/hit/three/ref8" -- [B4][B5]
      run := do
        expectOkStack "hit-three-ref8"
          (runDictUMinRefDirect #[.cell dictThreeRef8, intV 8])
          #[.cell valueA, intV 1, intV (-1)]
    }
    ,
    { name := "unit/hit/single/ref16" -- [B4][B5]
      run := do
        expectOkStack "hit-single-ref16"
          (runDictUMinRefDirect #[.cell dictSingleRef16, intV 16])
          #[.cell valueA, intV 256, intV (-1)]
    }
    ,
    { name := "unit/hit/single/ref256" -- [B4][B5][B6]
      run := do
        expectOkStack "hit-single-ref256"
          (runDictUMinRefDirect #[.cell dictSingleRef256, intV 256])
          #[.cell valueA, intV 0, intV (-1)]
    }
    ,
    { name := "unit/hit/min-width-mismatch" -- [B4][B6]
      run := do
        expectErr "miss-mismatch" (runDictUMinRefDirect #[.cell dictSingleRef8, intV 16]) .cellUnd
    }
    ,
    { name := "unit/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictUMinRefDirect #[]) .stkUnd
    }
    ,
    { name := "unit/underflow-one" -- [B2]
      run := do
        expectErr "underflow-one" (runDictUMinRefDirect #[intV 8]) .stkUnd
    }
    ,
    { name := "unit/err/nan" -- [B2]
      run := do
        expectErr "n-nan" (runDictUMinRefDirect #[dictNull, .int .nan]) .rangeChk
    }
    ,
    { name := "unit/err/n-negative" -- [B2]
      run := do
        expectErr "n-negative" (runDictUMinRefDirect #[dictNull, intV (-1)]) .rangeChk
    }
    ,
    { name := "unit/err/n-too-large" -- [B2]
      run := do
        expectErr "n-too-large" (runDictUMinRefDirect #[dictNull, intV 257]) .rangeChk
    }
    ,
    { name := "unit/err/root-type-tuple" -- [B3]
      run := do
        expectErr "root-tuple" (runDictUMinRefDirect #[.tuple #[], intV 8]) .typeChk
    }
    ,
    { name := "unit/err/root-type-cont" -- [B3]
      run := do
        expectErr "root-cont" (runDictUMinRefDirect #[.cont (.quit 0), intV 8]) .typeChk
    }
    ,
    { name := "unit/err/byref-bad-bits" -- [B6]
      run := do
        expectOkStack
          "byref-bad-bits"
          (runDictUMinRefDirect #[.cell dictByRefBadBits, intV 8])
          #[.cell byRefBadBits, intV 5, intV (-1)]
    }
    ,
    { name := "unit/err/byref-bad-no-refs" -- [B6]
      run := do
        expectOkStack
          "byref-bad-no-refs"
          (runDictUMinRefDirect #[.cell dictByRefBadNoRefs, intV 8])
          #[.cell byRefBadNoRefs, intV 5, intV (-1)]
    }
    ,
    { name := "unit/err/byref-bad-two-refs" -- [B6]
      run := do
        expectOkStack
          "byref-bad-two-refs"
          (runDictUMinRefDirect #[.cell dictByRefBadTwoRefs, intV 8])
          #[.cell byRefBadTwoRefs, intV 5, intV (-1)]
    }
    ,
    { name := "unit/err/malformed-root" -- [B11]
      run := do
        expectErr "malformed-root" (runDictUMinRefDirect #[.cell malformedDict, intV 8]) .cellUnd
    }
    ,
    { name := "unit/asm/encode-valid" -- [B8]
      run := do
        match assembleCp0 [dictUMinRefInstr] with
        | .ok c =>
            if c.bits = natToBits 0xF487 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF487, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"expected assemble success, got {e}")
    }
    ,
    { name := "unit/asm/reject-gap" -- [B8]
      run := do
        expectAssembleErr "asm-gap-1" (.dictGetMinMax 1) .invOpcode
    }
    ,
    { name := "unit/asm/reject-gap/family" -- [B8]
      run := do
        expectAssembleErr "asm-gap-24" (.dictGetMinMax 24) .invOpcode
    }
    ,
    { name := "unit/asm/reject-range" -- [B8]
      run := do
        expectAssembleErr "asm-range" (.dictGetMinMax 33) .rangeChk
    }
    ,
    { name := "unit/decode/family" -- [B9]
      run := do
        expectDecodeOk "decode-f482" rawOpcodeF482 (.dictGetMinMax 2)
        expectDecodeOk "decode-f483" rawOpcodeF483 (.dictGetMinMax 3)
        expectDecodeOk "decode-f484" rawOpcodeF484 (.dictGetMinMax 4)
        expectDecodeOk "decode-f485" rawOpcodeF485 (.dictGetMinMax 5)
        expectDecodeOk "decode-f486" rawOpcodeF486 (.dictGetMinMax 6)
        expectDecodeOk "decode-f487" rawOpcodeF487 (.dictGetMinMax 7)
    }
    ,
    { name := "unit/decode/errors" -- [B9]
      run := do
        expectDecodeErr "decode-f488" rawOpcodeF488 .invOpcode
        expectDecodeErr "decode-f489" rawOpcodeF489 .invOpcode
        expectDecodeErr "decode-truncated" rawOpcodeF4 .invOpcode
    }
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" #[dictNull, intV 0], -- [B3]
    mkCase "oracle/miss/null/1" #[dictNull, intV 1], -- [B3]
    mkCase "oracle/miss/null/8" #[dictNull, intV 8], -- [B3]
    mkCase "oracle/miss/null/16" #[dictNull, intV 16], -- [B3]
    mkCase "oracle/miss/null/256" #[dictNull, intV 256], -- [B3][B6]
    mkCase "oracle/miss/mismatch-width" #[.cell dictSingleRef8, intV 16], -- [B4]
    mkCase "oracle/hit/single/ref0" #[.cell dictSingleRef0, intV 0], -- [B4][B5]
    mkCase "oracle/hit/single/ref8" #[.cell dictSingleRef8, intV 8], -- [B4][B5]
    mkCase "oracle/hit/two/ref8" #[.cell dictTwoRef8, intV 8], -- [B4][B5]
    mkCase "oracle/hit/three/ref8" #[.cell dictThreeRef8, intV 8], -- [B4][B5]
    mkCase "oracle/hit/single/ref16" #[.cell dictSingleRef16, intV 16], -- [B4][B5]
    mkCase "oracle/hit/single/ref256" #[.cell dictSingleRef256, intV 256], -- [B4][B5][B6]
    mkCase "oracle/hit/two/ref256" #[.cell dictTwoRef256, intV 256], -- [B4][B5]
    mkCase "oracle/underflow/empty" #[], -- [B2]
    mkCase "oracle/underflow/one" #[intV 8], -- [B2]
    mkCase "oracle/err/nan" #[.cell dictSingleRef8, .int .nan], -- [B2]
    mkCase "oracle/err/n-negative" #[.cell dictSingleRef8, intV (-1)], -- [B2]
    mkCase "oracle/err/n-too-large" #[.cell dictSingleRef8, intV 257], -- [B2]
    mkCase "oracle/err/root-type-tuple" #[.tuple #[], intV 8], -- [B3]
    mkCase "oracle/err/root-type-cont" #[.cont (.quit 0), intV 8], -- [B3]
    mkCase "oracle/err/byref-bad-bits" #[.cell dictByRefBadBits, intV 8], -- [B6]
    mkCase "oracle/err/byref-bad-no-refs" #[.cell dictByRefBadNoRefs, intV 8], -- [B6]
    mkCase "oracle/err/byref-bad-two-refs" #[.cell dictByRefBadTwoRefs, intV 8], -- [B6]
    mkCase "oracle/err/malformed-root" #[.cell malformedDict, intV 8], -- [B11]
    mkCase "oracle/asm/encode" #[dictNull, intV 8] #[dictUMinRefInstr], -- [B8]
    mkRawCase "oracle/raw/f482" #[.cell dictSingleRef8, intV 8] rawOpcodeF482, -- [B9]
    mkRawCase "oracle/raw/f483" #[.cell dictSingleRef8, intV 8] rawOpcodeF483, -- [B9]
    mkRawCase "oracle/raw/f484" #[.cell dictSingleRef8, intV 8] rawOpcodeF484, -- [B9]
    mkRawCase "oracle/raw/f485" #[.cell dictSingleRef8, intV 8] rawOpcodeF485, -- [B9]
    mkRawCase "oracle/raw/f486" #[.cell dictSingleRef8, intV 8] rawOpcodeF486, -- [B9]
    mkRawCase "oracle/raw/f487" #[.cell dictSingleRef8, intV 8] rawOpcodeF487, -- [B9]
    mkRawCase "oracle/raw/f488" #[] rawOpcodeF488, -- [B9]
    mkRawCase "oracle/raw/f489" #[] rawOpcodeF489, -- [B9]
    mkRawCase "oracle/raw/f4" #[] rawOpcodeF4, -- [B9]
    mkCase "oracle/gas/exact-null" #[dictNull, intV 8]
      (#[.pushInt (.num dictUMinRefExactGas), .tonEnvOp .setGasLimit, dictUMinRefInstr])
      dictUMinRefGasExact, -- [B10]
    mkCase "oracle/gas/exact-minus-one-null" #[dictNull, intV 8]
      (#[.pushInt (.num dictUMinRefExactGasMinusOne), .tonEnvOp .setGasLimit, dictUMinRefInstr])
      dictUMinRefGasExactMinusOne, -- [B10]
    mkRawCase "oracle/raw/gap-f489" #[] rawOpcodeF489, -- [B9]
    mkRawCase "oracle/raw/truncated-f4" #[] rawOpcodeF4, -- [B9]
    mkCase "oracle/err/byref-good-shape" #[.cell dictByRefGood, intV 8], -- [B5][B6]
    mkCase "oracle/hit/raw-single-ref8" #[.cell dictByRefGood, intV 8], -- [B4][B5]
    mkCase "oracle/hit/single-ref-1" #[.cell dictSingleRef1, intV 1] -- [B4][B5][B6]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTUMINRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUMINREF
