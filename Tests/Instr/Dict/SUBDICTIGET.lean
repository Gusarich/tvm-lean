import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.SUBDICTIGET

/-!
INSTRUCTION: SUBDICTIGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch:
   - `execInstrDictExt` handles only `.dictExt (.subdictGet ..)`, otherwise delegates to `next`.
2. [B2] Stack arity:
   - `checkUnderflow 4` rejects too-short stacks.
3. [B3] `n` parsing:
   - `.natUpTo 1023` for `n`; non-int and out-of-range fail.
4. [B4] Root typing:
   - root must be `.cell` or `.null`; other values are `.typeChk`.
5. [B5] `k` parsing:
   - `k` parsed with `Nat.min mk n`, where `mk = 257` for signed int and `256` for unsigned int.
6. [B6] Key source validation:
   - int-key mode reads `Int`, slice-key mode reads `Slice`.
7. [B7] Key conversion/availability:
   - int-key out-of-range and short slice keys fail with `.cellUnd`.
8. [B8] Prefix extraction:
   - `k = 0` can return unchanged root; `k > 0` may return sub-root or `null`.
9. [B9] Malformed dictionary behavior:
   - malformed trie emits `.dictErr`.
10. [B10] Assembler behavior:
    - `.subdictGet` opcodes in this range are encodable by CP0.
    - Assembly roundtrips through `decodeCp0WithBits` with 16-bit encoding.
11. [B11] Decoder behavior:
   - `0xF4B1`, `0xF4B2`, `0xF4B3` are valid; `0xF4B0`, `0xF4B4`, `0xF4` are invalid.
12. [B12] Gas accounting:
   - exact gas succeeds; exact-minus-one fails.

TOTAL BRANCHES: 12
-/

private def subdictIGETId : InstrId := { name := "SUBDICTIGET" }

private def subdictSlice : Instr := .dictExt (.subdictGet false false false)
private def subdictInt : Instr := .dictExt (.subdictGet true false false)
private def subdictUInt : Instr := .dictExt (.subdictGet true true false)

private def raw16 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 16) #[]
private def raw8 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 8) #[]

private def rawF4B1 : Cell := raw16 0xF4B1
private def rawF4B2 : Cell := raw16 0xF4B2
private def rawF4B3 : Cell := raw16 0xF4B3
private def rawF4B0 : Cell := raw16 0xF4B0
private def rawF4B4 : Cell := raw16 0xF4B4
private def rawF4 : Cell := raw8 0xF4

private def dispatchSentinel : Int := 12_345

private def markerSlice (marker : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits marker 16) #[])

private def markerA : Slice := markerSlice 0xA1
private def markerB : Slice := markerSlice 0xB2
private def markerC : Slice := markerSlice 0xC3
private def markerD : Slice := markerSlice 0xD4

private def requireBits (label : String) (key : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? key n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: unsupported key {key} for n={n} unsigned={unsigned}"

private def mkDictFromIntPairs
    (label : String) (n : Nat) (unsigned : Bool) (pairs : Array (Int × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        let key : Int := pair.1
        let value : Slice := pair.2
        match st with
        | some root =>
            match dictSetSliceWithCells (some root) (requireBits label key n unsigned) value .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            match dictSetSliceWithCells none (requireBits label key n unsigned) value .set with
            | .ok (some root, _, _, _) => some root
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build dictionary"

private def mkDictFromSlicePairs (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        let bits : BitString := pair.1
        let value : Slice := pair.2
        match st with
        | some root =>
            match dictSetSliceWithCells (some root) bits value .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            match dictSetSliceWithCells none bits value .set with
            | .ok (some root, _, _, _) => some root
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build dictionary"

private def dictSliceRoot : Cell :=
  mkDictFromSlicePairs
    "dictSliceRoot"
    #[
      (natToBits 0x00 8, markerA),
      (natToBits 0x40 8, markerB),
      (natToBits 0x80 8, markerC),
      (natToBits 0xFF 8, markerD)
    ]

private def dictIntRoot : Cell :=
  mkDictFromIntPairs "dictIntRoot" 8 false #[(0, markerA), (5, markerB), (-1, markerC)]

private def dictUIntRoot : Cell :=
  mkDictFromIntPairs "dictUIntRoot" 8 true #[(0, markerB), (5, markerC), (255, markerD)]

private def malformedDictCell : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def subdictIGETGasExact : Int := computeExactGasBudget subdictSlice
private def subdictIGETGasExactMinusOne : Int := computeExactGasBudgetMinusOne subdictSlice
private def gasExact : OracleGasLimits := oracleGasLimitsExact subdictIGETGasExact
private def gasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne subdictIGETGasExactMinusOne

private def expectDecodeInvOpcode (label : String) (w : Nat) : IO Unit := do
  let s : Slice := Slice.ofCell (raw16 w)
  match decodeCp0WithBits s with
  | .ok (_, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, got success")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, got {e}")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected invOpcode")
  | .error .invOpcode => pure ()
  | .error e =>
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

private def runSubdictIGETDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runSubdictIGETDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV dispatchSentinel)) stack

private def subdictResultFromBits (root : Option Cell) (n : Nat) (bits : BitString) (k : Nat) : Value :=
  match dictExtractPrefixSubdictWithCells root n bits k false with
  | .ok (some c, _, _, _) => .cell c
  | .ok (none, _, _, _) => .null
  | .error e => panic! s!"SUBDICTIGET extraction failed: {reprStr e}"

private def stackInt (dict : Value) (key : Int) (k : Int) (n : Int) : Array Value :=
  #[intV key, intV k, dict, intV n]

private def stackSlice (dict : Value) (bits : BitString) (k : Int) (n : Int) : Array Value :=
  #[.slice (mkSliceFromBits bits), intV k, dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[subdictSlice])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := subdictIGETId
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
    instr := subdictIGETId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genSUBDICTIGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 :=
    if shape = 0 then
      mkCase (s!"{tag}/fuzz/signed-hit") (stackInt (.cell dictIntRoot) 5 8 8) (program := #[subdictInt])
    else if shape = 1 then
      mkCase (s!"{tag}/fuzz/unsigned-hit") (stackInt (.cell dictUIntRoot) 255 8 8) (program := #[subdictUInt])
    else if shape = 2 then
      mkCase (s!"{tag}/fuzz/slice-hit") (stackSlice (.cell dictSliceRoot) (natToBits 64 4) 4 8)
    else if shape = 3 then
      mkCase (s!"{tag}/fuzz/signed-k0") (stackInt (.cell dictIntRoot) 5 0 8) (program := #[subdictInt])
    else if shape = 4 then
      mkCase (s!"{tag}/fuzz/unsigned-k0") (stackInt (.cell dictUIntRoot) 5 0 8) (program := #[subdictUInt])
    else if shape = 5 then
      mkCase (s!"{tag}/fuzz/signed-miss") (stackInt (.cell dictIntRoot) 7 8 8) (program := #[subdictInt])
    else if shape = 6 then
      mkCase (s!"{tag}/fuzz/unsigned-miss") (stackInt (.cell dictUIntRoot) 7 8 8) (program := #[subdictUInt])
    else if shape = 7 then
      mkCase (s!"{tag}/fuzz/slice-miss") (stackSlice (.cell dictSliceRoot) (natToBits 1 4) 4 8)
    else if shape = 8 then
      mkCase (s!"{tag}/fuzz/null-root") (stackInt .null 5 2 8) (program := #[subdictInt])
    else if shape = 9 then
      mkCase (s!"{tag}/fuzz/slice-null-root") (stackSlice .null (natToBits 64 4) 4 8)
    else if shape = 10 then
      mkCase (s!"{tag}/fuzz/malformed-root") (stackInt (.cell malformedDictCell) 5 8 8) (program := #[subdictInt])
    else if shape = 11 then
      mkCase (s!"{tag}/fuzz/underflow-0") #[]
    else if shape = 12 then
      mkCase (s!"{tag}/fuzz/underflow-1") #[intV 8]
    else if shape = 13 then
      mkCase (s!"{tag}/fuzz/underflow-2") #[intV 8, .cell dictIntRoot]
    else if shape = 14 then
      mkCase (s!"{tag}/fuzz/underflow-3") #[intV 8, .cell dictIntRoot, intV 8]
    else if shape = 15 then
      mkCase (s!"{tag}/fuzz/n-type") (#[.cell dictIntRoot, intV 5, intV 8, .null])
    else if shape = 16 then
      mkCase (s!"{tag}/fuzz/n-nan") (#[.cell dictIntRoot, intV 5, intV 8, .int .nan])
    else if shape = 17 then
      mkCase (s!"{tag}/fuzz/n-negative") (#[.cell dictIntRoot, intV 5, intV 8, intV (-1)])
    else if shape = 18 then
      mkCase (s!"{tag}/fuzz/n-too-large") (#[.cell dictIntRoot, intV 5, intV 8, intV 1024])
    else if shape = 19 then
      mkCase (s!"{tag}/fuzz/k-type") (#[.cell dictIntRoot, intV 5, .tuple #[], intV 8])
    else if shape = 20 then
      mkCase (s!"{tag}/fuzz/k-negative") (#[.cell dictIntRoot, intV 5, intV (-1), intV 8])
    else if shape = 21 then
      mkCase (s!"{tag}/fuzz/k-signed-overflow") (#[.cell dictIntRoot, intV 5, intV 258, intV 300]) (program := #[subdictInt])
    else if shape = 22 then
      mkCase (s!"{tag}/fuzz/k-unsigned-overflow") (#[.cell dictUIntRoot, intV 5, intV 257, intV 300]) (program := #[subdictUInt])
    else if shape = 23 then
      mkCase (s!"{tag}/fuzz/key-type-int-in-slice") (#[.slice (mkSliceFromBits (natToBits 1 8)), .cell dictSliceRoot, intV 2, intV 8])
    else if shape = 24 then
      mkCase (s!"{tag}/fuzz/key-type-slice-in-int") (#[.int (.num 5), .cell dictIntRoot, intV 2, intV 8]) (program := #[subdictInt])
    else if shape = 25 then
      mkCase (s!"{tag}/fuzz/key-nan") (#[.cell dictIntRoot, .int .nan, intV 2, intV 8]) (program := #[subdictInt])
    else if shape = 26 then
      mkCase (s!"{tag}/fuzz/key-int-signed-over") (stackInt (.cell dictIntRoot) 128 8 8) (program := #[subdictInt])
    else if shape = 27 then
      mkCase (s!"{tag}/fuzz/key-int-signed-under") (stackInt (.cell dictIntRoot) (-129) 8 8) (program := #[subdictInt])
    else if shape = 28 then
      mkCase (s!"{tag}/fuzz/key-int-unsigned-over") (stackInt (.cell dictUIntRoot) 256 8 8) (program := #[subdictUInt])
    else if shape = 29 then
      mkCase (s!"{tag}/fuzz/key-int-unsigned-under") (stackInt (.cell dictUIntRoot) (-1) 8 8) (program := #[subdictUInt])
    else if shape = 30 then
      mkCase (s!"{tag}/fuzz/key-short") (stackSlice (.cell dictSliceRoot) (natToBits 1 1) 8 8)
    else if shape = 31 then
      mkCaseCode (s!"{tag}/fuzz/raw/f4b1") #[] rawF4B1
    else if shape = 32 then
      mkCaseCode (s!"{tag}/fuzz/raw/f4b2") #[] rawF4B2
    else if shape = 33 then
      mkCaseCode (s!"{tag}/fuzz/raw/f4b3") #[] rawF4B3
    else if shape = 34 then
      mkCaseCode (s!"{tag}/fuzz/raw/f4b0") #[] rawF4B0
    else if shape = 35 then
      mkCaseCode (s!"{tag}/fuzz/raw/f4b4") #[] rawF4B4
    else if shape = 36 then
      mkCaseCode (s!"{tag}/fuzz/raw/f4") #[] rawF4
    else if shape = 37 then
      mkCase
        (s!"{tag}/fuzz/gas/exact")
        (stackInt (.cell dictIntRoot) 5 8 8)
        (program := #[.pushInt (.num subdictIGETGasExact), .tonEnvOp .setGasLimit, subdictInt])
        gasExact
    else if shape = 38 then
      mkCase
        (s!"{tag}/fuzz/gas/exact-minus-one")
        (stackInt (.cell dictIntRoot) 5 8 8)
        (program := #[.pushInt (.num subdictIGETGasExactMinusOne), .tonEnvOp .setGasLimit, subdictInt])
        gasExactMinusOne
    else
      mkCase (s!"{tag}/fuzz/slice-deep") (stackSlice (.cell dictSliceRoot) (natToBits 255 8) 8 8)
  (case0, rng2)

def suite : InstrSuite where
  id := subdictIGETId
  unit := #[
      { name := "unit/dispatch/fallback"
        run := do
        expectOkStack
          "fallback/non-match"
          (runSubdictIGETDispatchFallback #[])
          (#[intV dispatchSentinel])
        expectOkStack
          "fallback/match"
          (runSubdictIGETDirect subdictInt (stackInt (.cell dictIntRoot) 5 8 8))
          #[subdictResultFromBits (some dictIntRoot) 8 (natToBits 5 8) 8] },
    { name := "unit/underflow-0"
      run := do
        expectErr "underflow/0" (runSubdictIGETDirect subdictSlice #[]) .stkUnd },
    { name := "unit/underflow-1"
      run := do
        expectErr "underflow/1" (runSubdictIGETDirect subdictSlice #[intV 8]) .stkUnd },
    { name := "unit/underflow-2"
      run := do
        expectErr "underflow/2" (runSubdictIGETDirect subdictSlice #[intV 8, .cell dictSliceRoot]) .stkUnd },
    { name := "unit/underflow-3"
      run := do
        expectErr "underflow/3" (runSubdictIGETDirect subdictSlice #[.slice (mkSliceFromBits (natToBits 1 8)), intV 2, .cell dictSliceRoot]) .stkUnd },
    { name := "unit/n-validation"
      run := do
        expectErr "n-type" (runSubdictIGETDirect subdictInt (#[intV 5, intV 8, .cell dictIntRoot, .null])) .typeChk
        expectErr "n-nan" (runSubdictIGETDirect subdictInt (#[intV 5, intV 8, .cell dictIntRoot, .int .nan])) .rangeChk
        expectErr "n-negative" (runSubdictIGETDirect subdictInt (#[intV 5, intV 8, .cell dictIntRoot, intV (-1)])) .rangeChk
        expectErr "n-too-large" (runSubdictIGETDirect subdictInt (#[intV 5, intV 8, .cell dictIntRoot, intV 1024])) .rangeChk },
    { name := "unit/root-type-and-k"
      run := do
        expectErr "root-type" (runSubdictIGETDirect subdictInt (#[intV 5, intV 2, .builder Builder.empty, intV 8])) .typeChk
        expectErr "k-type" (runSubdictIGETDirect subdictInt (#[intV 5, .tuple #[], .cell dictIntRoot, intV 8])) .typeChk
        expectErr "k-negative" (runSubdictIGETDirect subdictInt (#[intV 5, intV (-1), .cell dictIntRoot, intV 8])) .rangeChk
        expectErr "k-overflow-signed" (runSubdictIGETDirect subdictInt (#[intV 5, intV 258, .cell dictIntRoot, intV 300])) .rangeChk },
    { name := "unit/key-errors"
      run := do
        expectErr
          "key-type-int-in-slice"
          (runSubdictIGETDirect subdictSlice (#[intV 7, intV 2, .cell dictSliceRoot, intV 8])) .typeChk
        expectErr
          "key-type-slice-in-int"
          (runSubdictIGETDirect subdictInt (#[.slice (mkSliceFromBits (natToBits 1 8)), intV 2, .cell dictIntRoot, intV 8])) .typeChk
        expectErr
          "key-nan"
          (runSubdictIGETDirect subdictInt (#[.int .nan, intV 2, .cell dictIntRoot, intV 8])) .intOv },
    { name := "unit/key-conversion-fails"
      run := do
        expectErr "signed-overflow" (runSubdictIGETDirect subdictInt (stackInt (.cell dictIntRoot) 128 8 8)) .cellUnd
        expectErr "signed-underflow" (runSubdictIGETDirect subdictInt (stackInt (.cell dictIntRoot) (-129) 8 8)) .cellUnd
        expectErr "unsigned-overflow" (runSubdictIGETDirect subdictUInt (stackInt (.cell dictUIntRoot) 256 8 8)) .cellUnd
        expectErr "unsigned-underflow" (runSubdictIGETDirect subdictUInt (stackInt (.cell dictUIntRoot) (-1) 8 8)) .cellUnd
        expectErr "slice-short" (runSubdictIGETDirect subdictSlice (stackSlice (.cell dictSliceRoot) (natToBits 1 1) 8 8)) .cellUnd },
    { name := "unit/execution-hits"
      run := do
        expectOkStack
          "signed-hit"
          (runSubdictIGETDirect subdictInt (stackInt (.cell dictIntRoot) 5 8 8))
          #[subdictResultFromBits (some dictIntRoot) 8 (natToBits 5 8) 8]
        expectOkStack
          "unsigned-hit"
          (runSubdictIGETDirect subdictUInt (stackInt (.cell dictUIntRoot) 255 8 8))
          #[subdictResultFromBits (some dictUIntRoot) 8 (natToBits 255 8) 8]
        expectOkStack
          "slice-hit"
          (runSubdictIGETDirect subdictSlice (stackSlice (.cell dictSliceRoot) (natToBits 64 4) 4 8))
          #[subdictResultFromBits (some dictSliceRoot) 8 (natToBits 64 4) 4] },
    { name := "unit/execution-miss-and-root"
      run := do
        expectOkStack
          "k0-root"
          (runSubdictIGETDirect subdictInt (stackInt (.cell dictIntRoot) 0 0 8))
          #[.cell dictIntRoot]
        expectOkStack
          "signed-miss"
          (runSubdictIGETDirect subdictInt (stackInt (.cell dictIntRoot) 7 8 8))
          #[.null]
        expectOkStack
          "unsigned-miss"
          (runSubdictIGETDirect subdictUInt (stackInt (.cell dictUIntRoot) 7 8 8))
          #[.null]
        expectOkStack
          "slice-miss"
          (runSubdictIGETDirect subdictSlice (stackSlice (.cell dictSliceRoot) (natToBits 1 4) 4 8))
          #[.null]
        expectOkStack
          "null-root"
          (runSubdictIGETDirect subdictInt (stackInt .null 1 2 8))
          #[.null]
        expectOkStack
          "tail-preserved"
          (runSubdictIGETDirect subdictInt (#[intV 77, intV 5, intV 8, .cell dictIntRoot, intV 8]))
          #[intV 77, subdictResultFromBits (some dictIntRoot) 8 (natToBits 5 8) 8] },
    { name := "unit/malformed-and-codec"
      run := do
        expectErr
          "malformed-root"
          (runSubdictIGETDirect subdictInt (stackInt (.cell malformedDictCell) 5 8 8))
          .cellUnd
        expectAssembleExact "assemble/slice" subdictSlice 0xF4B1
        expectAssembleExact "assemble/int" subdictInt 0xF4B2
        expectAssembleExact "assemble/uint" subdictUInt 0xF4B3
        let _ ← expectDecodeStep "decode/f4b1" (Slice.ofCell rawF4B1) (.dictExt (.subdictGet false false false)) 16
        let _ ← expectDecodeStep "decode/f4b2" (Slice.ofCell rawF4B2) (.dictExt (.subdictGet true false false)) 16
        let _ ← expectDecodeStep "decode/f4b3" (Slice.ofCell rawF4B3) (.dictExt (.subdictGet true true false)) 16
        expectDecodeInvOpcode "decode/f4b0" 0xF4B0
        expectDecodeInvOpcode "decode/f4b4" 0xF4B4
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"decode/f4: expected invOpcode, got error {e}")
        | .ok (decoded, bits, _) =>
            throw (IO.userError s!"decode/f4: expected invOpcode, got {reprStr decoded}/{bits}")
      } ]
  oracle := #[
    mkCase "oracle/fallback" #[] (program := #[]), -- [B1]
    mkCase "oracle/fallback-match" (stackInt (.cell dictIntRoot) 5 8 8) (program := #[subdictInt]), -- [B1]
    mkCase "oracle/underflow-0" #[], -- [B2]
    mkCase "oracle/underflow-1" #[intV 8], -- [B2]
    mkCase "oracle/underflow-2" #[intV 8, .cell dictSliceRoot], -- [B2]
    mkCase "oracle/underflow-3" (stackSlice (.cell dictSliceRoot) (natToBits 1 8) 2 8), -- [B2]
    mkCase "oracle/n-type" (#[.cell dictIntRoot, intV 5, intV 8, .null]), -- [B3]
    mkCase "oracle/n-nan" (#[.cell dictIntRoot, intV 5, intV 8, .int .nan]), -- [B3]
    mkCase "oracle/n-negative" (#[.cell dictIntRoot, intV 5, intV 8, intV (-1)]), -- [B3]
    mkCase "oracle/n-too-large" (#[.cell dictIntRoot, intV 5, intV 8, intV 1024]), -- [B3]
    mkCase "oracle/root-type" (#[.builder Builder.empty, intV 5, intV 2, intV 8]), -- [B4]
    mkCase "oracle/root-null" (stackInt .null 5 8 8), -- [B4]
    mkCase "oracle/k-type" (#[.cell dictIntRoot, intV 5, .tuple #[], intV 8]), -- [B5]
    mkCase "oracle/k-negative" (#[.cell dictIntRoot, intV 5, intV (-1), intV 8]), -- [B5]
    mkCase "oracle/k-overflow-signed" (#[.cell dictIntRoot, intV 5, intV 258, intV 300]), -- [B5]
    mkCase "oracle/k-overflow-unsigned" (#[.cell dictUIntRoot, intV 5, intV 257, intV 300]), -- [B5]
    mkCase "oracle/key-type-int-in-slice" (#[.cell dictSliceRoot, .slice (mkSliceFromBits (natToBits 1 8)), intV 2, intV 8]), -- [B6]
    mkCase "oracle/key-type-slice-in-int" (#[.cell dictIntRoot, .int (.num 5), intV 2, intV 8]), -- [B6]
    mkCase "oracle/key-nan" (#[.cell dictIntRoot, .int .nan, intV 2, intV 8]), -- [B6]
    mkCase "oracle/signed-key-overflow" (stackInt (.cell dictIntRoot) 128 8 8), -- [B7]
    mkCase "oracle/signed-key-underflow" (stackInt (.cell dictIntRoot) (-129) 8 8), -- [B7]
    mkCase "oracle/unsigned-key-overflow" (stackInt (.cell dictUIntRoot) 256 8 8), -- [B7]
    mkCase "oracle/unsigned-key-underflow" (stackInt (.cell dictUIntRoot) (-1) 8 8), -- [B7]
    mkCase "oracle/slice-key-short" (stackSlice (.cell dictSliceRoot) (natToBits 1 1) 8 8), -- [B7]
    mkCase "oracle/signed-hit" (stackInt (.cell dictIntRoot) 5 8 8) (program := #[subdictInt]), -- [B8]
    mkCase "oracle/unsigned-hit" (stackInt (.cell dictUIntRoot) 255 8 8) (program := #[subdictUInt]), -- [B8]
    mkCase "oracle/slice-hit" (stackSlice (.cell dictSliceRoot) (natToBits 64 4) 4 8), -- [B8]
    mkCase "oracle/signed-k0" (stackInt (.cell dictIntRoot) 5 0 8) (program := #[subdictInt]), -- [B8]
    mkCase "oracle/signed-miss" (stackInt (.cell dictIntRoot) 7 8 8) (program := #[subdictInt]), -- [B8]
    mkCase "oracle/unsigned-miss" (stackInt (.cell dictUIntRoot) 7 8 8) (program := #[subdictUInt]), -- [B8]
    mkCase "oracle/slice-miss" (stackSlice (.cell dictSliceRoot) (natToBits 1 4) 4 8), -- [B8]
    mkCase "oracle/malformed" (stackInt (.cell malformedDictCell) 5 8 8) (program := #[subdictInt]), -- [B9]
    mkCaseCode "oracle/raw/f4b1" #[] rawF4B1, -- [B11]
    mkCaseCode "oracle/raw/f4b2" #[] rawF4B2, -- [B11]
    mkCaseCode "oracle/raw/f4b3" #[] rawF4B3, -- [B11]
    mkCaseCode "oracle/raw/f4b0" #[] rawF4B0, -- [B11]
    mkCaseCode "oracle/raw/f4b4" #[] rawF4B4, -- [B11]
    mkCaseCode "oracle/raw/f4" #[] rawF4, -- [B11]
    mkCase
      "oracle/gas-exact"
      (stackInt (.cell dictIntRoot) 5 8 8)
      (program := #[.pushInt (.num subdictIGETGasExact), .tonEnvOp .setGasLimit, subdictInt])
      gasExact, -- [B12]
    mkCase
      "oracle/gas-exact-minus-one"
      (stackInt (.cell dictIntRoot) 5 8 8)
      (program := #[.pushInt (.num subdictIGETGasExactMinusOne), .tonEnvOp .setGasLimit, subdictInt])
      gasExactMinusOne, -- [B12]
    mkCase
      "oracle/gas-slice"
      (stackSlice (.cell dictSliceRoot) (natToBits 64 4) 4 8)
      (program := #[.pushInt (.num subdictIGETGasExact), .tonEnvOp .setGasLimit, subdictSlice])
      gasExact -- [B12]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr subdictIGETId
      count := 500
      gen := genSUBDICTIGETFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.SUBDICTIGET
