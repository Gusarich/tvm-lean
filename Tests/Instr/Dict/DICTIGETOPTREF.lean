import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETOPTREF

/-!
INSTRUCTION: DICTIGETOPTREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path
- `execInstrDictExt` only handles `.dictExt` opcodes; unmatched instructions must run `next`.

2. [B2] Runtime key-path split and stack-pop contract
- `VM.checkUnderflow 3` always requires `n`, `dict?`, and key-like argument.
- `n` is parsed via `popNatUpTo 1023`; negative values / `NaN` / out-of-range values hit `rangeChk`.
- `dictCell?` comes from `popMaybeCell` and is optional.
- For `intKey = true`, key is `popIntFinite` and converted with `dictKeyBits?`.
- For `intKey = false`, key is `popSlice` and must have at least `n` bits.

3. [B3] Integer-key branch behavior
- On invalid int key (`dictKeyBits? = none`), Lean/C++ push `.null`.
- On valid int key, run lookup.

4. [B4] Slice-key branch behavior
- `dict-key` extraction requires enough bits in key slice; otherwise `cellUnd`.

5. [B5] Lookup/return semantics
- Empty/missing key path returns `.null`.
- Hit path extracts the looked-up value as a reference via `extractRefOrThrow`:
  `bitsRemaining == 0 ∧ refsRemaining == 1` required.
- Malformed payload shape triggers `dictErr`.

6. [B6] Decode mapping / boundary coverage
- `0xf46a` = `.dictExt (.getOptRef true false)`
- `0xf46b` = `.dictExt (.getOptRef true true)`
- `0xf469` = `.dictExt (.getOptRef false false)`
- Neighbor opcodes should not decode as this instruction.

7. [B7] Assembly boundary
- `Asm/Cp0.lean` does not encode `.dictExt` instructions (`.invOpcode`).

8. [B8] Gas accounting
- Base instruction cost is fixed (`instrGas`).
- Runtime lookup path includes dynamic accounting in dictionary traversal helpers.
- Exact budget and exact-minus-one oracle cases are required.

9. [B9] Fuzz coverage
- Fuzz must cover signed/unsigned variants, hit/miss, malformed payloads, type/range/underflow branches.

Total branches tracked: 9.
-/

private def dictIGetOptRefId : InstrId :=
  { name := "DICTIGETOPTREF" }

private def dictIGetOptRefInstr (intKey unsigned : Bool) : Instr :=
  .dictExt (.getOptRef intKey unsigned)

private def dictIGetOptRefCode (intKey unsigned : Bool) : Nat :=
  0xf469 ||| (if intKey then 2 else 0) ||| (if unsigned then 1 else 0)

private def dictIGetOptRefCell (intKey unsigned : Bool) : Cell :=
  Cell.mkOrdinary (natToBits (dictIGetOptRefCode intKey unsigned) 16) #[]

private def rawCell16 (w16 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w16 16) #[]

private def dispatchSentinel : Int := 771_001

private def valueLeafA : Cell :=
  Cell.mkOrdinary #[] #[Cell.mkOrdinary (natToBits 0xa5 8) #[]]

private def valueLeafB : Cell :=
  Cell.mkOrdinary #[] #[Cell.mkOrdinary (natToBits 0x5a 8) #[]]

private def valueLeafBits : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def valueLeafNoRef : Cell :=
  Cell.mkOrdinary #[] #[]

private def valueLeafTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[valueLeafA, valueLeafB]

private def mkKeyBits (label : String) (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid key ({idx}, n={n}, unsigned={unsigned})"

private def mkDictRefRootFromBits (label : String) (keyBits : BitString) (value : Cell) : Cell :=
  match dictSetRefWithCells none keyBits value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | _ => panic! s!"{label}: dictSetRefWithCells failed"

private def mkDictRefRootFromBits2
    (label : String)
    (keyBits1 : BitString) (value1 : Cell)
    (keyBits2 : BitString) (value2 : Cell) : Cell :=
  let r1 := mkDictRefRootFromBits (s!"{label}/1") keyBits1 value1
  match dictSetRefWithCells (some r1) keyBits2 value2 .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | _ => panic! s!"{label}/2: second dict insertion failed"

private def mkDictRefRoot (label : String) (idx : Int) (n : Nat) (unsigned : Bool) (value : Cell) : Cell :=
  mkDictRefRootFromBits label (mkKeyBits label idx n unsigned) value

private def signedNibbleRoot4 : Cell :=
  mkDictRefRootFromBits2
    "signed-root4"
    (mkKeyBits "signed-root4/key-a" (-3) 4 false) valueLeafA
    (mkKeyBits "signed-root4/key-b" (4) 4 false) valueLeafB

private def unsignedNibbleRoot4 : Cell :=
  mkDictRefRootFromBits2
    "unsigned-root4"
    (mkKeyBits "unsigned-root4/key-a" 5 4 true) valueLeafA
    (mkKeyBits "unsigned-root4/key-b" 9 4 true) valueLeafB

private def sliceRoot4 : Cell :=
  mkDictRefRootFromBits2
    "slice-root4"
    (natToBits 2 4) valueLeafA
    (natToBits 7 4) valueLeafB

private def signedNibbleBadValueRoot4 : Cell :=
  mkDictRefRoot
    "signed-bad-value-root4"
    (-3) 4 false valueLeafBits

private def unsignedNibbleBadValueRoot4 : Cell :=
  mkDictRefRoot
    "unsigned-bad-value-root4"
    5 4 true valueLeafTwoRefs

private def sliceBadValueRoot4 : Cell :=
  mkDictRefRootFromBits "slice-bad-value-root4" (natToBits 2 4) valueLeafNoRef

private def signedRootZero : Cell :=
  mkDictRefRoot "signed-root0" 0 0 false valueLeafA

private def unsignedRootZero : Cell :=
  mkDictRefRoot "unsigned-root0" 0 0 true valueLeafB

private def mkIntStack (dict : Value) (key : Int) (n : Int) : Array Value :=
  #[dict, intV key, intV n]

private def mkSliceStack (dict : Value) (n : Int) (keyBits : BitString) : Array Value :=
  #[dict, .slice (mkSliceFromBits keyBits), intV n]

private def mkCase
    (name : String)
    (instr : Instr)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIGetOptRefId
    program := #[instr]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (i, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr i}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def runDictIGetOptRefFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV dispatchSentinel)) stack

private def runDictIGetOptRefDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def dictIGetOptRefGas : Int :=
  computeExactGasBudget (dictIGetOptRefInstr false false)

private def dictIGetOptRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictIGetOptRefGas

private def dictIGetOptRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictIGetOptRefGas

private def genDictIGetOptRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (tag, rng2) := randNat rng1 0 999_999
  let (case, rngFinal) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase s!"fuzz/signed/hit/{tag}" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-3) 4), rng2)
    else if shape = 1 then
      (mkCase s!"fuzz/signed/miss/{tag}" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) 6 4), rng2)
    else if shape = 2 then
      (mkCase s!"fuzz/signed/out-of-range-high/{tag}" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) 8 4), rng2)
    else if shape = 3 then
      (mkCase s!"fuzz/signed/out-of-range-low/{tag}" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-9) 4), rng2)
    else if shape = 4 then
      (mkCase s!"fuzz/unsigned/hit/{tag}" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) 5 4), rng2)
    else if shape = 5 then
      (mkCase s!"fuzz/unsigned/miss/{tag}" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) 1 4), rng2)
    else if shape = 6 then
      (mkCase s!"fuzz/unsigned/out-of-range/{tag}" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) (-1) 4), rng2)
    else if shape = 7 then
      (mkCase s!"fuzz/slice/hit/{tag}" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 2 4)), rng2)
    else if shape = 8 then
      (mkCase s!"fuzz/slice/miss/{tag}" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 3 4)), rng2)
    else if shape = 9 then
      (mkCase s!"fuzz/slice/underflow/{tag}" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 8 (natToBits 2 4)), rng2)
    else if shape = 10 then
      (mkCase s!"fuzz/signed/malformed-refshape/{tag}" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleBadValueRoot4) (-3) 4), rng2)
    else if shape = 11 then
      (mkCase s!"fuzz/unsigned/malformed-refshape/{tag}" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleBadValueRoot4) 5 4), rng2)
    else if shape = 12 then
      (mkCase s!"fuzz/slice/malformed-refshape/{tag}" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceBadValueRoot4) 4 (natToBits 2 4)), rng2)
    else if shape = 13 then
      (mkCase s!"fuzz/n-range/{tag}" (dictIGetOptRefInstr true false) #[.cell signedNibbleRoot4, intV 3, intV (-1)], rng2)
    else
      (mkCase s!"fuzz/type-error/{tag}" (dictIGetOptRefInstr true false) #[.cell signedNibbleRoot4, .null, intV 4], rng2)
  (case, rngFinal)

/--
`genDictIGetOptRefFuzzCase` intentionally avoids exhaustive generation to keep corpus
compact while still exercising the most important branches from LEAN/C++ parity analysis.
-/

def suite : InstrSuite where
  id := dictIGetOptRefId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch-fallback"
          (runDictIGetOptRefFallback (dictIGetOptRefInstr true false) #[])
          #[intV dispatchSentinel]
    }
    ,
    { name := "unit/decoder/decode/slice"
      run := do
        let _ ← expectDecodeStep "decode/slice"
          (mkSliceFromBits (natToBits 0xf469 16))
          (dictIGetOptRefInstr false false)
          16
    }
    ,
    { name := "unit/decoder/decode/signed"
      run := do
        let _ ← expectDecodeStep "decode/signed"
          (mkSliceFromBits (natToBits 0xf46a 16))
          (dictIGetOptRefInstr true false)
          16
    }
    ,
    { name := "unit/decoder/decode/unsigned"
      run := do
        let _ ← expectDecodeStep "decode/unsigned"
          (mkSliceFromBits (natToBits 0xf46b 16))
          (dictIGetOptRefInstr true true)
          16
    }
    ,
    { name := "unit/decoder/decode/below"
      run := expectDecodeInvOpcode "decode/f468" 0xf468
    }
    ,
    { name := "unit/decoder/decode/above"
      run := expectDecodeInvOpcode "decode/f46c" 0xf46c
    }
    ,
    { name := "unit/decoder/decode/truncated4bit"
      run := expectDecodeInvOpcode "decode/short4" 0xf
    }
    ,
    { name := "unit/asm/not-supported"
      run := do
        match assembleCp0 [dictIGetOptRefInstr true true] with
        | .ok _ =>
            throw (IO.userError "expected .invOpcode on assemble, got success")
        | .error e =>
            if e = .invOpcode then
              pure ()
            else
              throw (IO.userError s!"expected .invOpcode, got {e}")
    }
    ,
    { name := "unit/runtime/int/signed-hit"
      run := do
        expectOkStack "runtime/int/signed-hit"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-3) 4))
          #[.cell valueLeafA]
    }
    ,
    { name := "unit/runtime/int/signed-miss"
      run := do
        expectOkStack "runtime/int/signed-miss"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) 6 4))
          #[.null]
    }
    ,
    { name := "unit/runtime/int/signed-out-of-range-high-null"
      run := do
        expectOkStack "runtime/int/signed-out-of-range-high-null"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) 8 4))
          #[.null]
    }
    ,
    { name := "unit/runtime/int/unsigned-hit"
      run := do
        expectOkStack "runtime/int/unsigned-hit"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) 5 4))
          #[.cell valueLeafA]
    }
    ,
    { name := "unit/runtime/int/unsigned-negative-null"
      run := do
        expectOkStack "runtime/int/unsigned-negative-null"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) (-1) 4))
          #[.null]
    }
    ,
    { name := "unit/runtime/slice/hit"
      run := do
        expectOkStack "runtime/slice-hit"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 2 4)))
          #[.cell valueLeafA]
    }
    ,
    { name := "unit/runtime/slice/miss"
      run := do
        expectOkStack "runtime/slice-miss"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 4 4)))
          #[.null]
    }
    ,
    { name := "unit/runtime/slice/underflow"
      run := do
        expectErr "runtime/slice-underflow"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 8 (natToBits 2 4)))
          .cellUnd
    }
    ,
    { name := "unit/runtime/n-range-negative"
      run := do
        expectErr "runtime/n-negative" (
          runDictIGetOptRefDirect (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-1 : Int) (-1))
        ) .rangeChk
    }
    ,
    { name := "unit/runtime/n-range-large"
      run := do
        expectErr "runtime/n-too-large"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) 4 1024))
          .rangeChk
    }
    ,
    { name := "unit/runtime/n-nan"
      run := do
        expectErr "runtime/n-nan"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) #[.cell signedNibbleRoot4, intV 1, .int .nan])
          .rangeChk
    }
    ,
    { name := "unit/runtime/underflow"
      run := do
        expectErr "runtime/underflow"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) #[.cell signedNibbleRoot4, intV 1])
          .stkUnd
    }
    ,
    { name := "unit/runtime/type-error-int-key"
      run := do
        expectErr "runtime/type-error-int-key"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) #[.cell signedNibbleRoot4, .tuple #[], intV 4])
          .typeChk
    }
    ,
    { name := "unit/runtime/type-error-slice-key"
      run := do
        expectErr "runtime/type-error-slice-key"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr false false) #[.cell sliceRoot4, .int (.num 2), intV 4])
          .typeChk
    }
    ,
    { name := "unit/runtime/type-error-dict"
      run := do
        expectErr "runtime/type-error-dict"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) #[.builder Builder.empty, intV 2, intV 4])
          .typeChk
    }
    ,
    { name := "unit/runtime/dictErr-malformed-int-value"
      run := do
        expectErr "runtime/dictErr-malformed-int-value"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleBadValueRoot4) (-3) 4))
          .dictErr
    }
    ,
    { name := "unit/runtime/dictErr-malformed-slice-value"
      run := do
        expectErr "runtime/dictErr-malformed-slice-value"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceBadValueRoot4) 4 (natToBits 2 4)))
          .dictErr
    }
    ,
    { name := "unit/runtime/n-zero/signed-hit"
      run := do
        expectOkStack "runtime/n-zero-signed-hit"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true false) (mkIntStack (.cell signedRootZero) 0 0))
          #[.cell valueLeafA]
    }
    ,
    { name := "unit/runtime/n-zero/unsigned-miss"
      run := do
        expectOkStack "runtime/n-zero-unsigned-miss"
          (runDictIGetOptRefDirect (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedRootZero) 1 0))
          #[.null]
    }
  ]
  oracle := #[
    mkCase "oracle/int/signed/hit" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-3) 4)
    ,
    mkCase "oracle/int/signed/hit/alternate" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) 4 4)
    ,
    mkCase "oracle/int/signed/miss" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (6) 4)
    ,
    mkCase "oracle/int/signed/out-of-range-high" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) 8 4)
    ,
    mkCase "oracle/int/signed/out-of-range-low" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-9) 4)
    ,
    mkCase "oracle/int/signed/out-of-range-zero-key" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedRootZero) 1 0)
    ,
    mkCase "oracle/int/signed/n-zero-hit" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedRootZero) 0 0)
    ,
    mkCase "oracle/int/signed/underflow-nil-root" (dictIGetOptRefInstr true false) (mkIntStack (.null) (-3) 4)
    ,
    mkCase "oracle/int/unsigned/hit" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) 5 4)
    ,
    mkCase "oracle/int/unsigned/alternate-hit" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) 9 4)
    ,
    mkCase "oracle/int/unsigned/miss" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) 7 4)
    ,
    mkCase "oracle/int/unsigned/out-of-range-high" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) 16 4)
    ,
    mkCase "oracle/int/unsigned/out-of-range-negative" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleRoot4) (-1) 4)
    ,
    mkCase "oracle/int/unsigned/zero-key-hit" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedRootZero) 0 0)
    ,
    mkCase "oracle/slice/hit" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 2 4))
    ,
    mkCase "oracle/slice/hit-alt" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 7 4))
    ,
    mkCase "oracle/slice/miss" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 0 4))
    ,
    mkCase "oracle/slice/miss-empty-root" (dictIGetOptRefInstr false false) (mkSliceStack (.null) 4 (natToBits 3 4))
    ,
    mkCase "oracle/slice/n-zero-hit" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 0 #[])
    ,
    mkCase "oracle/slice/n-underflow" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 8 (natToBits 2 4))
    ,
    mkCase "oracle/slice/bad-ref-shape" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceBadValueRoot4) 4 (natToBits 2 4))
    ,
    mkCase "oracle/int/bad-ref-shape" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleBadValueRoot4) (-3) 4)
    ,
    mkCase "oracle/int/unsigned-bad-ref-shape" (dictIGetOptRefInstr true true) (mkIntStack (.cell unsignedNibbleBadValueRoot4) 5 4)
    ,
    mkCase "oracle/int/type-error-key" (dictIGetOptRefInstr true false) #[.cell signedNibbleRoot4, .null, intV 4]
    ,
    mkCase "oracle/slice/type-error-key" (dictIGetOptRefInstr false false) #[.cell sliceRoot4, .null, intV 4]
    ,
    mkCase "oracle/int/type-error-dict" (dictIGetOptRefInstr true false) #[.slice (mkSliceFromBits (natToBits 2 4)), intV 3, intV 4]
    ,
    mkCase "oracle/int/range-n-negative" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-3) (-1))
    ,
    mkCase "oracle/int/range-n-nan" (dictIGetOptRefInstr true false) #[.cell signedNibbleRoot4, intV 3, .int .nan]
    ,
    mkCase "oracle/slice/underflow-two" (dictIGetOptRefInstr false false) #[.cell sliceRoot4, .slice (mkSliceFromBits (natToBits 2 2)), intV 4]
    ,
    mkCase "oracle/underflow-empty-stack" (dictIGetOptRefInstr true false) #[]
    ,
    mkCase "oracle/underflow-two" (dictIGetOptRefInstr true false) #[.cell signedNibbleRoot4, intV 1]
    ,
    mkCase "oracle/gas/exact-hit" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 2 4)) dictIGetOptRefGasExact
    ,
    mkCase "oracle/gas/exact-minus-one-hit" (dictIGetOptRefInstr false false) (mkSliceStack (.cell sliceRoot4) 4 (natToBits 2 4)) dictIGetOptRefGasExactMinusOne
    ,
    mkCase "oracle/gas/exact-hit-int" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-3) 4) dictIGetOptRefGasExact
    ,
    mkCase "oracle/gas/exact-minus-one-hit-int" (dictIGetOptRefInstr true false) (mkIntStack (.cell signedNibbleRoot4) (-3) 4) dictIGetOptRefGasExactMinusOne
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr dictIGetOptRefId
      count := 500
      gen := genDictIGetOptRefFuzzCase
    }
  ]

end Tests.Instr.Dict.DICTIGETOPTREF
