import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTIMINREF

/-!
INSTRUCTION: DICTIMINREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatcher reachability branch.
   - `execInstrDictDictGetMinMax` must only handle `.dictGetMinMax`;
     non-matching instructions must fall through to `next`.

2. [B2] Preamble stack/type validation.
   - `checkUnderflow 2` validates required stack height.
   - `popNatUpTo 257` rejects NaN, negative width, and out-of-range width.
   - `popMaybeCell` accepts `null` and `.cell`; everything else is `.typeChk`.

3. [B3] Missing-key path.
   - Empty dict (`null`) or traversal miss must push only `0`.
   - No dictionary root is pushed for non-remove variants.

4. [B4] Hit path.
   - Dict traversal with by-ref payload and minimum-integer-order must push:
     `foundValue`, reconstructed signed key, and success flag `-1`.

5. [B5] Signed-key reconstruction and boundary widths.
   - `n = 0` and `n = 257` are valid.
   - `bitsToIntSignedTwos` applies to the extracted key bits.

6. [B6] By-ref payload structure.
   - On hit, return payload must satisfy `bitsRemaining = 0` and `refsRemaining = 1`;
     any mismatch raises `.dictErr`.

7. [B7] Assembler constraints.
   - `.dictGetMinMax 5` is valid and encodes to `0xF485`.
   - Gaps in argument families are `.invOpcode`.
   - `args5 > 31` is `.rangeChk`.

8. [B8] Decoder behavior.
   - Family boundaries decode to neighboring `.dictGetMinMax` values.
   - Gaps and short code should decode with `.invOpcode`.

9. [B9] Dictionary structural errors.
   - Traversal into a malformed root can raise `.cellUnd` or `.dictErr` depending on shape.

10. [B10] Gas accounting.
   - Base gas is fixed for this non-delete variant; exact and exact-minus-one
     are the two gas branches.

TOTAL BRANCHES: 10

Each oracle test below is tagged with one or more [Bn].
-/

private def dictIMinRefId : InstrId :=
  { name := "DICTIMINREF" }

private def dictIMinRefInstr : Instr :=
  .dictGetMinMax 5

private def dictIMinRefExactGas : Int :=
  computeExactGasBudget dictIMinRefInstr

private def dictIMinRefExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictIMinRefInstr

private def dictIMinRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictIMinRefExactGas

private def dictIMinRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictIMinRefExactGasMinusOne

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def dispatchSentinel : Int := 77_777

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for e in entries do
      let (k, v) := e
      let keyBits :=
        match dictKeyBits? k n false with
        | some bits => bits
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}): {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for e in entries do
      let (k, v) := e
      let keyBits :=
        match dictKeyBits? k n false with
        | some bits => bits
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}): {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def badByRefSlice : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0xF0 8) #[])

private def dictNull : Value := .null

private def dictSingleRef8 : Cell :=
  mkDictSetRefRoot! "dictSingleRef8" 8 #[(5, valueA)]

private def dictTwoRef8 : Cell :=
  mkDictSetRefRoot! "dictTwoRef8" 8 #[(5, valueA), (-1, valueB)]

private def dictThreeRef8 : Cell :=
  mkDictSetRefRoot! "dictThreeRef8" 8 #[(5, valueA), (-12, valueB), (9, valueC)]

private def dictSingleRef257 : Cell :=
  mkDictSetRefRoot! "dictSingleRef257" 257 #[(0, valueA)]

private def dictTwoRef257 : Cell :=
  mkDictSetRefRoot! "dictTwoRef257" 257 #[(minInt257, valueA), (maxInt257, valueB)]

private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(7, badByRefSlice)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b0 1) #[]

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
    (program : Array Instr := #[dictIMinRefInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIMinRefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIMinRefId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictIMinRefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV dispatchSentinel)) stack

private def runDictIMinRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax dictIMinRefInstr stack

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
        throw (IO.userError s!"{label}: unexpected decode suffix")
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

private def genDICTIMinRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/8" #[dictNull, intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/16" #[dictNull, intV 16], rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null/257" #[dictNull, intV 257], rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/single8" #[.cell dictSingleRef8, intV 8], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/two8" #[.cell dictTwoRef8, intV 8], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/three8" #[.cell dictThreeRef8, intV 8], rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/single257" #[.cell dictSingleRef257, intV 257], rng1)
    else if shape = 8 then
      (mkCase "fuzz/hit/two257" #[.cell dictTwoRef257, intV 257], rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/underflow-one" #[dictNull], rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/type-root" #[.tuple #[], intV 8], rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type-nan" #[dictNull, .int .nan], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/type-negative-n" #[.cell dictSingleRef8, intV (-1)], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/type-wide-n" #[.cell dictSingleRef8, intV 258], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/byref-shape" #[.cell dictSliceSingle8, intV 8], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/malformed-root" #[.cell malformedDict, intV 8], rng1)
    else if shape = 17 then
      (mkRawCase "fuzz/raw/f485" #[.cell dictSingleRef8, intV 8] rawOpcodeF485, rng1)
    else if shape = 18 then
      (mkCase "fuzz/gas/exact" #[dictNull, intV 8]
        (#[.pushInt (.num dictIMinRefExactGas), .tonEnvOp .setGasLimit, dictIMinRefInstr])
        (dictIMinRefGasExact), rng1)
    else if shape = 19 then
      (mkCase "fuzz/gas/exact-minus-one" #[dictNull, intV 8]
        (#[.pushInt (.num dictIMinRefExactGasMinusOne), .tonEnvOp .setGasLimit, dictIMinRefInstr])
        (dictIMinRefGasExactMinusOne), rng1)
    else
      (mkRawCase "fuzz/raw/f488" #[.cell dictSingleRef8, intV 8] rawOpcodeF488, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr dictIMinRefId

def suite : InstrSuite where
  id := dictIMinRefId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDictIMinRefDispatchFallback #[.cell dictSingleRef8, intV 8] with
        | .ok st =>
            if st == #[.cell dictSingleRef8, intV 8, intV dispatchSentinel] then
              pure ()
            else
              throw (IO.userError s!"fallback failed, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"fallback failed, got exception {e}")
    }
    ,
    { name := "unit/exec/miss/null/8" -- [B3][B2]
      run := do
        expectOkStack "miss-null-8" (runDictIMinRefDirect #[dictNull, intV 8]) #[intV 0]
    }
    ,
    { name := "unit/exec/miss/null/0" -- [B3][B5]
      run := do
        expectOkStack "miss-null-0" (runDictIMinRefDirect #[dictNull, intV 0]) #[intV 0]
    }
    ,
    { name := "unit/exec/hit/single/ref8" -- [B4]
      run := do
        expectOkStack "hit-single-ref8"
          (runDictIMinRefDirect #[.cell dictSingleRef8, intV 8])
          #[.cell valueA, intV 5, intV (-1)]
    }
    ,
    { name := "unit/exec/hit/two/ref8/min" -- [B4]
      run := do
        expectOkStack "hit-two-ref8"
          (runDictIMinRefDirect #[.cell dictTwoRef8, intV 8])
          #[.cell valueB, intV (-1), intV (-1)]
    }
    ,
    { name := "unit/exec/hit/three/ref8/min" -- [B4][B6]
      run := do
        expectOkStack "hit-three-ref8"
          (runDictIMinRefDirect #[.cell dictThreeRef8, intV 8])
          #[.cell valueB, intV (-12), intV (-1)]
    }
    ,
    { name := "unit/exec/hit/two/ref257/min" -- [B4][B6]
      run := do
        expectOkStack "hit-two-ref257"
          (runDictIMinRefDirect #[.cell dictTwoRef257, intV 257])
          #[.cell valueA, intV minInt257, intV (-1)]
    }
    ,
    { name := "unit/exec/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictIMinRefDirect #[]) .stkUnd
    }
    ,
    { name := "unit/exec/underflow-one" -- [B2]
      run := do
        expectErr "underflow-one" (runDictIMinRefDirect #[intV 8]) .stkUnd
    }
    ,
    { name := "unit/exec/err/nan" -- [B2][B5]
      run := do
        expectErr "nan" (runDictIMinRefDirect #[dictNull, .int .nan]) .rangeChk
    }
    ,
    { name := "unit/exec/err/negative-width" -- [B2]
      run := do
        expectErr "negative-width" (runDictIMinRefDirect #[dictNull, intV (-1)]) .rangeChk
    }
    ,
    { name := "unit/exec/err/too-large-width" -- [B2]
      run := do
        expectErr "too-large-width" (runDictIMinRefDirect #[dictNull, intV 258]) .rangeChk
    }
    ,
    { name := "unit/exec/err/root-type" -- [B2]
      run := do
        expectErr "root-tuple" (runDictIMinRefDirect #[.tuple #[], intV 8]) .typeChk
        expectErr "root-cont" (runDictIMinRefDirect #[.cont (.quit 0), intV 8]) .typeChk
    }
    ,
    { name := "unit/exec/err/byref-shape" -- [B6]
      run := do
        expectErr "bad-ref-shape" (runDictIMinRefDirect #[.cell dictSliceSingle8, intV 8]) .dictErr
    }
    ,
    { name := "unit/exec/err/malformed-root" -- [B9]
      run := do
        expectErr "malformed-root" (runDictIMinRefDirect #[.cell malformedDict, intV 8]) .cellUnd
    }
    ,
    { name := "unit/asm/encode-ok" -- [B7]
      run := do
        match assembleCp0 [dictIMinRefInstr] with
        | .ok c =>
            if c.bits = natToBits 0xF485 16 then
              pure ()
            else
              throw (IO.userError s!"expected DICTIMINREF encode, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"expected DICTIMINREF assembly success, got {e}")
    }
    ,
    { name := "unit/asm/reject-gap" -- [B7]
      run := do
        expectAssembleErr "asm-reject-gap" (.dictGetMinMax 24) .invOpcode
    }
    ,
    { name := "unit/asm/reject-range" -- [B7]
      run := do
        expectAssembleErr "asm-reject-range" (.dictGetMinMax 33) .rangeChk
    }
    ,
    { name := "unit/decode/family" -- [B8]
      run := do
        expectDecodeOk "decode-f482" rawOpcodeF482 (.dictGetMinMax 2)
        expectDecodeOk "decode-f483" rawOpcodeF483 (.dictGetMinMax 3)
        expectDecodeOk "decode-f484" rawOpcodeF484 (.dictGetMinMax 4)
        expectDecodeOk "decode-self" rawOpcodeF485 (.dictGetMinMax 5)
        expectDecodeOk "decode-f486" rawOpcodeF486 (.dictGetMinMax 6)
        expectDecodeOk "decode-f487" rawOpcodeF487 (.dictGetMinMax 7)
        expectDecodeErr "decode-gap" rawOpcodeF488 .invOpcode
    }
    ,
    { name := "unit/decode/gap-and-trunc" -- [B8]
      run := do
        expectDecodeErr "decode-gap-gap" rawOpcodeF489 .invOpcode
        expectDecodeErr "decode-truncated" rawOpcodeF4 .invOpcode
    }
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" #[dictNull, intV 0], -- [B3][B5]
    mkCase "oracle/miss/null/8" #[dictNull, intV 8], -- [B3]
    mkCase "oracle/miss/null/16" #[dictNull, intV 16], -- [B3]
    mkCase "oracle/miss/null/257" #[dictNull, intV 257], -- [B3]
    mkCase "oracle/miss/too-wide-key" #[dictNull, intV 257], -- [B3][B5]
    mkCase "oracle/miss/hit-width-mismatch" #[.cell dictSingleRef8, intV 16], -- [B3]
    mkCase "oracle/hit/single/ref8" #[.cell dictSingleRef8, intV 8], -- [B4]
    mkCase "oracle/hit/two/ref8" #[.cell dictTwoRef8, intV 8], -- [B4]
    mkCase "oracle/hit/three/ref8" #[.cell dictThreeRef8, intV 8], -- [B4]
    mkCase "oracle/hit/single/ref257" #[.cell dictSingleRef257, intV 257], -- [B4][B5]
    mkCase "oracle/hit/two/ref257" #[.cell dictTwoRef257, intV 257], -- [B4][B6]
    mkCase "oracle/hit/min-8-neg" #[.cell dictTwoRef8, intV 8], -- [B4][B6]
    mkCase "oracle/hit/min-257-edge" #[.cell dictTwoRef257, intV 257], -- [B4][B6]
    mkCase "oracle/underflow/empty" #[], -- [B2]
    mkCase "oracle/underflow/one" #[dictNull], -- [B2]
    mkCase "oracle/err/root-tuple" #[.tuple #[], intV 8], -- [B2]
    mkCase "oracle/err/root-cont" #[.cont (.quit 0), intV 8], -- [B2]
    mkCase "oracle/err/nan" #[dictNull, .int .nan], -- [B2]
    mkCase "oracle/err/n-negative" #[.cell dictSingleRef8, intV (-1)], -- [B2][B5]
    mkCase "oracle/err/n-too-large" #[.cell dictSingleRef8, intV 9999], -- [B2]
    mkCase "oracle/err/n-edge-258" #[.cell dictSingleRef8, intV 258], -- [B2]
    mkCase "oracle/err/byref-shape" #[.cell dictSliceSingle8, intV 8], -- [B6]
    mkCase "oracle/err/malformed-root" #[.cell malformedDict, intV 8], -- [B9]
    mkCase "oracle/asm/exact" #[dictNull, intV 8]
      (#[.pushInt (.num dictIMinRefExactGas), .tonEnvOp .setGasLimit, dictIMinRefInstr])
      (dictIMinRefGasExact), -- [B10]
    mkCase "oracle/gas/exact-minus-one" #[dictNull, intV 8]
      (#[.pushInt (.num dictIMinRefExactGasMinusOne), .tonEnvOp .setGasLimit, dictIMinRefInstr])
      (dictIMinRefGasExactMinusOne), -- [B10]
    mkRawCase "oracle/raw/f482" #[] rawOpcodeF482, -- [B8]
    mkRawCase "oracle/raw/f483" #[] rawOpcodeF483, -- [B8]
    mkRawCase "oracle/raw/f484" #[] rawOpcodeF484, -- [B8]
    mkRawCase "oracle/raw/f485" #[] rawOpcodeF485, -- [B8]
    mkRawCase "oracle/raw/f486" #[] rawOpcodeF486, -- [B8]
    mkRawCase "oracle/raw/f487" #[] rawOpcodeF487, -- [B8]
    mkRawCase "oracle/raw/gap-f488" #[] rawOpcodeF488, -- [B8]
    mkRawCase "oracle/raw/gap-f489" #[] rawOpcodeF489, -- [B8]
    mkRawCase "oracle/raw/truncated-f4" #[] rawOpcodeF4, -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTIMinRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIMINREF
