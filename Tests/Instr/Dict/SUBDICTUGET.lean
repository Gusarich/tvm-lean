import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.SUBDICTUGET

/-!
INSTRUCTION: SUBDICTUGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch behavior.
   - `execInstrDictExt` handles `.dictExt (.subdictGet ..)`.
   - Non-dictExt instructions must fall through via `next`.
2. [B2] Stack arity/type guard.
   - `checkUnderflow 4` requires four operands on stack: key, k, dict, n.
   - Non-int `n` and non-int `k` are type errors.
3. [B3] `n` bounds validation.
   - `popNatUpTo 1023` accepts only naturals and rejects .nan/negative/>1023 with .rangeChk.
4. [B4] Dictionary operand validation.
   - `popMaybeCell` accepts `.null` and `.cell`; tuples/builders are .typeChk.
5. [B5] Prefix-length validation for unsigned mode.
   - `k` is bounded by `min 256 n`; out-of-range .rangeChk, .nan .rangeChk.
6. [B6] Key materialization.
   - Key is read through `popIntFinite`.
   - .nan key is .intOv.
   - `dictKeyBits?` is called with width `k`.
7. [B7] Out-of-range integer key conversion.
   - For unsigned key mode, negative or too-wide values map to `.cellUnd`.
8. [B8] Prefix extraction k=0.
   - no root precharge and the returned dictionary root is unchanged.
9. [B9] Prefix extraction k>0.
   - malformed trie triggers `.dictErr`.
   - prefix miss returns `.null`.
   - matched prefixes may rebuild labels with `.cell` root and set `created`.
10. [B10] Decoder boundaries.
    - valid decode: 0xf4b3.
    - invalid decode: 0xf4b2, 0xf4b4, 0xf4b8, 0xf4b0, truncated streams.
11. [B11] Assembler behavior.
    - SUBDICTUGET is encodable by CP0 (`0xf4b3`) and roundtrips through `decodeCp0WithBits`.
12. [B12] Gas.
    - base cost exact/exact-1
    - surcharge branch for rebuild created>0.

TOTAL BRANCHES: 12
-/

private def suiteId : InstrId := { name := "SUBDICTUGET" }

private def subdictUGET : Instr := .dictExt (.subdictGet true true false)

private def raw16 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 16) #[]

private def rawF4B2 : Cell := raw16 0xF4B2
private def rawF4B3 : Cell := raw16 0xF4B3
private def rawF4B4 : Cell := raw16 0xF4B4
private def rawF4B8 : Cell := raw16 0xF4B8
private def rawF4B0 : Cell := raw16 0xF4B0
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]
private def rawF4Trunc15 : Cell := Cell.mkOrdinary (natToBits (0xF4B3 >>> 1) 15) #[]

private def dispatchSentinel : Int := 12_345

private def markerSlice (marker : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits marker 16) #[])

private def markerA : Slice := markerSlice 0xa1
private def markerB : Slice := markerSlice 0xa2
private def markerC : Slice := markerSlice 0xa3
private def markerD : Slice := markerSlice 0xa4
private def markerE : Slice := markerSlice 0xa5
private def markerF : Slice := markerSlice 0xa6

private def requireBits (label : String) (key : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? key n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: unsupported key {key} for n={n} unsigned={unsigned}"

private def mkDictFromPairs (label : String) (n : Nat) (pairs : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let key : Int := pair.1
      let value : Slice := pair.2
      let bits : BitString := requireBits label key n true
      match dictSetSliceWithCells root bits value .set with
      | .ok (some next, _, _, _) =>
          root := some next
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected none during dict build"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict"

private def dictU4Root : Cell :=
  mkDictFromPairs "dictU4Root" 4 #[
    (0, markerA),
    (8, markerB),
    (12, markerC),
    (15, markerD)
  ]

private def dictU8Root : Cell :=
  mkDictFromPairs "dictU8Root" 8 #[
    (0, markerE),
    (1, markerF),
    (5, markerA),
    (255, markerB),
    (42, markerC)
  ]

private def dictU0Root : Cell :=
  mkDictFromPairs "dictU0Root" 0 #[(0, markerD)]

private def malformedDictCell : Cell := Cell.mkOrdinary (natToBits 2 2) #[]
private def malformedDictCell2 : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def subdictResult (root : Cell) (n : Nat) (key : Int) (k : Nat) : Value :=
  match dictKeyBits? key k true with
  | none => .null
  | some keyBits =>
      match dictExtractPrefixSubdictWithCells (some root) n keyBits k false with
      | .ok (some c, _, _, _) => .cell c
      | .ok (none, _, _, _) => .null
      | .error e => panic! s!"dictExtractPrefixSubdictWithCells failed: {reprStr e}"

private def runSubdictUGETDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt subdictUGET stack

private def runSubdictUGETFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (.int (IntVal.num dispatchSentinel))) stack

private def opcodeSlice16 (w : Nat) : Slice := Slice.ofCell (raw16 w)

private def expectDecodeInvOpcode (label : String) (w : Nat) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 w) with
  | .ok (_, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, got success")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, got {e}")

private def expectAssembleInvOpcode (label : String) : IO Unit := do
  match assembleCp0 [subdictUGET] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected invOpcode, got bits {c.bits}")
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleExact (label : String) (i : Instr) (w16 : Nat) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble ok, got {e}")
  | .ok c =>
      if c.bits != natToBits w16 16 then
        throw (IO.userError s!"{label}: expected bits {reprStr (natToBits w16 16)}, got {reprStr c.bits}")
      let _ ← expectDecodeStep (s!"{label}/decode") (Slice.ofCell c) i 16
      pure ()

private def runGasBase : Int := computeExactGasBudget subdictUGET
private def runGasBaseMinusOne : Int := computeExactGasBudgetMinusOne subdictUGET
private def gasBase : OracleGasLimits := oracleGasLimitsExact runGasBase
private def gasBaseMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne runGasBaseMinusOne

private def subdictHitCreated : Nat :=
  match
    dictExtractPrefixSubdictWithCells (some dictU4Root) 4 (requireBits "SUBDICTUGET/created" 0 4 true) 1 false
  with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def runGasHit : Int := runGasBase + Int.ofNat subdictHitCreated * cellCreateGasPrice
private def runGasHitMinusOne : Int :=
  runGasBaseMinusOne + Int.ofNat subdictHitCreated * cellCreateGasPrice
private def gasHit : OracleGasLimits := oracleGasLimitsExact runGasHit
private def gasHitMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne runGasHitMinusOne

private def mkStackI (key : Int) (dict : Value) (n : Int) (k : Int) : Array Value :=
  #[intV key, intV k, dict, intV n]

private def mkStackV (key : Value) (dict : Value) (n : Value) (k : Value) : Array Value :=
  #[key, k, dict, n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[subdictUGET]) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[]) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genSubdictUGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase (s!"{tag}/fallback") #[] (program := #[])
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 1 then
      mkCase (s!"{tag}/or/[B2] underflow/empty") #[]
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 2 then
      mkCase (s!"{tag}/or/[B2] underflow/one") #[intV 0]
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 3 then
      mkCase (s!"{tag}/or/[B2] underflow/two") (mkStackI 0 (.cell dictU4Root) 8 0)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 4 then
      mkCase (s!"{tag}/or/[B3] n/nan") (mkStackV (intV 0) (.cell dictU4Root) (.int .nan) (intV 1))
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 5 then
      mkCase (s!"{tag}/or/[B3] n/negative") (mkStackI 0 (.cell dictU4Root) (-1) 1)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 6 then
      mkCase (s!"{tag}/or/[B3] n/too-large") (mkStackI 0 (.cell dictU4Root) 1024 1)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 7 then
      mkCase (s!"{tag}/or/[B5] k/negative") (mkStackI 0 (.cell dictU4Root) 8 (-1))
      |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 8 then
      mkCase (s!"{tag}/or/[B5] k/too-large-small") (mkStackI 0 (.cell dictU4Root) 4 5)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 9 then
      mkCase (s!"{tag}/or/[B5] k/too-large-large") (mkStackI 0 (.cell dictU8Root) 1023 257)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 10 then
      mkCase (s!"{tag}/or/[B4] dict-builder") (mkStackI 0 (.builder Builder.empty) 8 2)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 11 then
      mkCase (s!"{tag}/or/[B4] dict-tuple") (mkStackI 0 (.tuple #[]) 8 2)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 12 then
      mkCase (s!"{tag}/or/[B6] key-slice") (mkStackV (.slice (mkSliceFromBits (natToBits 1 1))) (.cell dictU4Root) (intV 4) (intV 4))
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 13 then
      mkCase (s!"{tag}/or/[B6] key-nan") (mkStackV (.int .nan) (.cell dictU4Root) (intV 4) (intV 4))
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 14 then
      mkCase (s!"{tag}/or/[B7] key/out-of-range-positive") (mkStackI 256 (.cell dictU8Root) 8 8)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 15 then
      mkCase (s!"{tag}/or/[B7] key/out-of-range-negative") (mkStackI (-1) (.cell dictU8Root) 8 8)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 16 then
      mkCase (s!"{tag}/or/[B7] key/out-of-range-zero") (mkStackI 1 (.cell dictU0Root) 0 0)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 17 then
      mkCase (s!"{tag}/or/[B9] miss/root-null") (mkStackI 7 (.null) 8 4)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 18 then
      mkCase (s!"{tag}/or/[B9] miss/prefix") (mkStackI 1 (.cell dictU8Root) 8 2)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 19 then
      mkCase (s!"{tag}/or/[B8] k0-root") (mkStackI 1 (.cell dictU8Root) 8 0)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 20 then
      mkCase (s!"{tag}/or/[B9] hit-k1-created") (mkStackI 0 (.cell dictU4Root) 4 1)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 21 then
      mkCaseCode (s!"{tag}/or/[B10] decode/valid") #[] rawF4B3
    else if shape = 22 then
      mkCaseCode (s!"{tag}/or/[B10] decode/signed-family") #[] rawF4B2
    else if shape = 23 then
      mkCaseCode (s!"{tag}/or/[B10] decode/invalid-low") #[] rawF4B4
    else if shape = 24 then
      mkCaseCode (s!"{tag}/or/[B10] decode/invalid-high") #[] rawF4B8
    else if shape = 25 then
      mkCaseCode (s!"{tag}/or/[B10] decode/trunc8") #[] rawF4
    else if shape = 26 then
      mkCaseCode (s!"{tag}/or/[B10] decode/trunc15") #[] rawF4Trunc15
    else if shape = 27 then
      mkCase (s!"{tag}/or/[B12] gas/exact-base") (mkStackI 0 (.cell dictU4Root) 4 1) gasBase
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 28 then
      mkCase (s!"{tag}/or/[B12] gas/exact-base-minus-one") (mkStackI 0 (.cell dictU4Root) 4 1) gasBaseMinusOne
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 29 then
      mkCase (s!"{tag}/or/[B12] gas/exact-hit") (mkStackI 0 (.cell dictU4Root) 4 1) gasHit
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 30 then
      mkCase (s!"{tag}/or/[B12] gas/exact-hit-minus-one") (mkStackI 0 (.cell dictU4Root) 4 1) gasHitMinusOne
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 31 then
      mkCase (s!"{tag}/or/[B9] k0-malformed-root") (mkStackI 0 (.cell malformedDictCell) 4 0)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 32 then
      mkCase (s!"{tag}/or/[B9] malformed-root") (mkStackI 0 (.cell malformedDictCell) 4 1)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 33 then
      mkCase (s!"{tag}/or/[B9] malformed-root2") (mkStackI 0 (.cell malformedDictCell2) 4 1)
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 34 then
      mkCase (s!"{tag}/or/[B2] underflow/dict") #[]
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 35 then
      mkCase (s!"{tag}/or/[B2] underflow/key") #[intV 1]
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 36 then
      mkCase (s!"{tag}/or/[B2] underflow/k") (#[intV 1, intV 2, .cell dictU4Root])
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 37 then
      mkCase (s!"{tag}/or/[B2] underflow/n") (#[intV 1, intV 2, .cell dictU4Root, intV 8])
        |> fun c => { c with codeCell? := some rawF4B3 }
    else if shape = 38 then
      mkCaseCode (s!"{tag}/or/[B10] decode/f4b0") #[] rawF4B0
    else
      mkCaseCode (s!"{tag}/or/[B11] decode/other") #[] rawF4B0
  let (tag2, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{tag2}/{case0.name}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "fallback/non-subdict" (runSubdictUGETFallback #[]) #[.int (IntVal.num dispatchSentinel)] },
    { name := "unit/underflow"
      run := do
        expectErr "underflow/0" (runSubdictUGETDirect #[]) .stkUnd
        expectErr "underflow/1" (runSubdictUGETDirect #[.int (IntVal.num 8)]) .stkUnd
        expectErr "underflow/2" (runSubdictUGETDirect #[.cell dictU4Root, intV 0]) .stkUnd
        expectErr "underflow/3" (runSubdictUGETDirect #[intV 0, intV 4, .cell dictU4Root]) .stkUnd },
    { name := "unit/n-validation"
      run := do
        expectErr "n/type"
          (runSubdictUGETDirect (mkStackV (intV 0) (.cell dictU8Root) (.slice markerA) (intV 0)))
          .typeChk
        expectErr "n/nan" (runSubdictUGETDirect (mkStackV (intV 8) (.cell dictU8Root) (.int .nan) (intV 8))) .rangeChk
        expectErr "n/negative" (runSubdictUGETDirect (mkStackV (intV 8) (.cell dictU8Root) (intV (-1)) (intV 8)) ) .rangeChk
        expectErr "n/too-large" (runSubdictUGETDirect (mkStackI 8 (.cell dictU8Root) 1024 8)) .rangeChk },
    { name := "unit/k-validation"
      run := do
        expectErr "k/type" (runSubdictUGETDirect (mkStackV (intV 8) (.cell dictU8Root) (intV 8) (.tuple #[])) ) .typeChk
        expectErr "k/nan" (runSubdictUGETDirect (mkStackV (intV 8) (.cell dictU8Root) (intV 8) (.int .nan)) ) .rangeChk
        expectErr "k/negative" (runSubdictUGETDirect (mkStackI 8 (.cell dictU8Root) 8 (-1)) ) .rangeChk
        expectErr "k/too-large-small-n" (runSubdictUGETDirect (mkStackI 8 (.cell dictU4Root) 4 5)) .rangeChk
        expectErr "k/too-large-large-n" (runSubdictUGETDirect (mkStackI 8 (.cell dictU8Root) 1023 257)) .rangeChk },
    { name := "unit/type-checks"
      run := do
        expectErr "dict-builder" (runSubdictUGETDirect (mkStackI 8 (.builder Builder.empty) 8 8)) .typeChk
        expectErr "dict-tuple" (runSubdictUGETDirect (mkStackI 8 (.tuple #[]) 8 8)) .typeChk },
    { name := "unit/key-materialization"
      run := do
        expectErr "key/type" (runSubdictUGETDirect (mkStackV (.slice markerA) (.cell dictU8Root) (intV 8) (intV 8))) .typeChk
        expectErr "key/nan" (runSubdictUGETDirect (mkStackV (.int .nan) (.cell dictU8Root) (intV 8) (intV 8))) .intOv
        expectErr "key/out-of-range-positive" (runSubdictUGETDirect (mkStackI 256 (.cell dictU8Root) 8 8)) .cellUnd
        expectErr "key/out-of-range-negative" (runSubdictUGETDirect (mkStackI (-1) (.cell dictU8Root) 8 8)) .cellUnd
        expectErr "key/out-of-range-n0" (runSubdictUGETDirect (mkStackI 1 (.cell dictU0Root) 0 0)) .cellUnd },
    { name := "unit/runtime/base-paths"
      run := do
        expectOkStack
          "k0-preserve-root"
          (runSubdictUGETDirect (mkStackI 0 (.cell dictU8Root) 8 0))
          #[.cell dictU8Root]
        expectOkStack
          "k0-null-root"
          (runSubdictUGETDirect (mkStackI 0 (.null) 8 0))
          #[.null]
        expectOkStack
          "miss-prefix"
          (runSubdictUGETDirect (mkStackI 1 (.cell dictU8Root) 8 2))
          #[subdictResult dictU8Root 8 1 2]
        expectOkStack
          "miss-root-null"
          (runSubdictUGETDirect (mkStackI 2 (.null) 8 2))
          #[.null]
        expectOkStack
          "hit-k1-created"
          (runSubdictUGETDirect (mkStackI 0 (.cell dictU4Root) 4 1))
          #[subdictResult dictU4Root 4 0 1] },
    { name := "unit/runtime/errors"
      run := do
        expectOkStack
          "k0-malformed-root"
          (runSubdictUGETDirect (mkStackI 0 (.cell malformedDictCell) 4 0))
          #[.cell malformedDictCell]
        expectErr "malformed-k2" (runSubdictUGETDirect (mkStackI 0 (.cell malformedDictCell2) 4 2)) .cellUnd },
    { name := "unit/assembler"
      run := expectAssembleExact "assemble-subdictug" subdictUGET 0xF4B3 },
    { name := "unit/decoder"
      run := do
        let _ ← expectDecodeStep "decode/f4b3" (opcodeSlice16 0xF4B3) (.dictExt (.subdictGet true true false)) 16
        let _ ← expectDecodeStep "decode/f4b2" (Slice.ofCell rawF4B2) (.dictExt (.subdictGet true false false)) 16
        expectDecodeInvOpcode "decode/f4b4" 0xF4B4
        expectDecodeInvOpcode "decode/f4b8" 0xF4B8
        expectDecodeInvOpcode "decode/f4b0" 0xF4B0
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"decode/f4: expected invOpcode, got error {e}")
        | .ok (decoded, bits, _) =>
            throw (IO.userError s!"decode/f4: expected invOpcode, got {reprStr decoded} ({bits} bits)") },
  ]
  oracle := #[
    mkCase "or/[B2] underflow/empty" #[]
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B2] underflow/one" #[intV 0]
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B2] underflow/two" (mkStackI 0 (.cell dictU4Root) 8 0)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B2] underflow/three" (mkStackI 0 (.cell dictU4Root) 8 0)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B3] n/type" (mkStackV (.slice markerA) (.cell dictU8Root) (intV 0) (intV 8))
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B3] n/nan" (mkStackV (intV 0) (.cell dictU8Root) (.int .nan) (intV 8))
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B3] n/negative" (mkStackV (intV 8) (.cell dictU8Root) (intV (-1)) (intV 8))
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B3] n/too-large" (mkStackI 8 (.cell dictU8Root) 1024 8)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B5] k/type" (mkStackV (intV 8) (.cell dictU8Root) (intV 8) (.tuple #[]))
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B5] k/nan" (mkStackV (intV 8) (.cell dictU8Root) (intV 8) (.int .nan))
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B5] k/negative" (mkStackI 8 (.cell dictU8Root) 8 (-1))
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B5] k/too-large-small" (mkStackI 8 (.cell dictU8Root) 4 5)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B5] k/too-large-large" (mkStackI 8 (.cell dictU8Root) 1023 257)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B4] dict/builder" (mkStackI 8 (.builder Builder.empty) 8 8)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B4] dict/tuple" (mkStackI 8 (.tuple #[]) 8 8)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B6] key/type" (mkStackV (.slice markerA) (.cell dictU8Root) (intV 8) (intV 8))
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B6] key/nan" (mkStackV (.int .nan) (.cell dictU8Root) (intV 8) (intV 8))
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B7] key/out-of-range-positive" (mkStackI 256 (.cell dictU8Root) 8 8)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B7] key/out-of-range-negative" (mkStackI (-1) (.cell dictU8Root) 8 8)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B7] key/out-of-range-n0" (mkStackI 1 (.cell dictU0Root) 0 0)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B9] runtime/k0-root" (mkStackI 7 (.cell dictU8Root) 8 0)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B9] runtime/k0-null" (mkStackI 7 (.null) 8 0)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B9] runtime/miss-prefix" (mkStackI 2 (.cell dictU8Root) 8 2)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B9] runtime/miss-null" (mkStackI 7 (.null) 8 2)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B9] runtime/hit-k1" (mkStackI 0 (.cell dictU4Root) 4 1)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B9] runtime/hit-root-unchanged" (mkStackI 0 (.cell dictU8Root) 8 0)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B9] runtime/malformed-k0" (mkStackI 0 (.cell malformedDictCell2) 4 0)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B9] runtime/error-malformed-k2" (mkStackI 0 (.cell malformedDictCell2) 4 2)
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCaseCode "or/raw/f4b3" #[] rawF4B3,
    mkCaseCode "or/raw/f4b2" #[] rawF4B2,
    mkCaseCode "or/raw/f4b4" #[] rawF4B4,
    mkCaseCode "or/raw/f4b8" #[] rawF4B8,
    mkCaseCode "or/raw/f4b0" #[] rawF4B0,
    mkCaseCode "or/raw/trunc8" #[] rawF4,
    mkCaseCode "or/raw/trunc15" #[] rawF4Trunc15,
    mkCase "or/[B12] gas/exact-base" (mkStackI 0 (.cell dictU4Root) 4 1) gasBase
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B12] gas/exact-base-minus-one" (mkStackI 0 (.cell dictU4Root) 4 1) gasBaseMinusOne
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B12] gas/exact-hit" (mkStackI 0 (.cell dictU4Root) 4 1) gasHit
      |> fun c => { c with codeCell? := some rawF4B3 },
    mkCase "or/[B12] gas/exact-hit-minus-one" (mkStackI 0 (.cell dictU4Root) 4 1) gasHitMinusOne
      |> fun c => { c with codeCell? := some rawF4B3 }
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genSubdictUGETFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.SUBDICTUGET
