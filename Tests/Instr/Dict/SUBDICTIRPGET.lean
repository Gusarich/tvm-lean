import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.SUBDICTIRPGET

/-!
INSTRUCTION: SUBDICTIRPGET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch.
   - `.dictExt (.subdictGet true false true)` is handled by `execInstrDictExt`.
   - Non-matching instructions must forward to `next`.

2. [B2] Runtime arity check.
   - `checkUnderflow 4` is enforced before any pops.
   - Stack shape is `[key, dict, k, n]` (top is `n`).

3. [B3] `n` validation.
   - `popNatUpTo 1023` accepts non-negative naturals in range.
   - `.typeChk` for non-int `n`.
   - `.rangeChk` for `.nan`, negative, or >1023.

4. [B4] Dictionary root validation.
   - `popMaybeCell` accepts `.cell` and `.null`.
   - `.typeChk` for non-cell/non-null values.

5. [B5] Prefix length (`k`) validation.
   - `k ← popNatUpTo (Nat.min 257 n)` in this signed-int variant.
   - `.typeChk` for non-int `k`.
   - `.rangeChk` when `k < 0` or `k > min 257 n`.

6. [B6] Key extraction (int path).
   - `popIntFinite` enforces integer input.
   - `.intOv` for `.nan`.
   - `dictKeyBits? key k false` is used with signed conversion.

7. [B7] Signed-out-of-range + special remap.
   - Out-of-range signed key returns `cellUnd` from conversion/mapping.
   - For `intKey=true`, `unsigned=false`, `rp=true` this becomes `.dictErr`.
   - Non-signed/non-rp variants do not take this remap.

8. [B8] `k = 0` fast path and `k > 0` path.
   - `k = 0` skips prefix-root precharge.
   - `k > 0` calls `prechargeRootLoad`.

9. [B9] Prefix extraction results.
   - Match pushes extracted RP sub-dictionary root.
   - Miss pushes `null`.
   - Malformed prefix traversal errors are propagated (subject to [B7]).

10. [B10] Assembler behavior.
   - `assembleCp0` for this `.dictExt` form is `.invOpcode`.

11. [B11] Decoder behavior.
   - `0xf4b6` -> `.dictExt (.subdictGet true false true)`.
   - `0xf4b5`/`0xf4b7` decode to neighboring RP variants.
   - `0xf4b4`, `0xf4b8`, truncated `0xf4` decode as `invOpcode`.

12. [B12] Gas.
   - `computeExactGasBudget` used for exact and exact-1 checks.
   - Changed-prefix success may include `created` surcharge.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def suiteId : InstrId := { name := "SUBDICTIRPGET" }

private def instr : Instr := .dictExt (.subdictGet true false true)
private def dispatchSentinel : Int := 13_579

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawF4b5 : Cell := raw16 0xf4b5
private def rawF4b6 : Cell := raw16 0xf4b6
private def rawF4b7 : Cell := raw16 0xf4b7
private def rawF4b4 : Cell := raw16 0xf4b4
private def rawF4b8 : Cell := raw16 0xf4b8
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def opcodeSlice16 (w : Nat) : Slice := Slice.ofCell (raw16 w)

private def markerSlice (marker : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits marker 16) #[])

private def markerOne : Slice := markerSlice 0xA1
private def markerTwo : Slice := markerSlice 0xB2
private def markerThree : Slice := markerSlice 0xC3
private def markerFour : Slice := markerSlice 0xD4

private def requireBits (label : String) (key : Int) (n : Nat) : BitString :=
  match dictKeyBits? key n false with
  | some bits => bits
  | none => panic! s!"{label}: key {key} out of range for n={n}"

private def mkDictFromPairs (label : String) (n : Nat) (pairs : Array (Int × Slice)) : Cell :=
  let rootOpt :=
    pairs.foldl
      (fun st p =>
        let (k, v) := p
        let bits := requireBits label k n
        match st with
        | some root =>
            match dictSetSliceWithCells (some root) bits v .set with
            | .ok (some next, _, _, _) => some next
            | .ok (none, _, _, _) => none
            | .error _ => none
        | none =>
            match dictSetSliceWithCells none bits v .set with
            | .ok (some root, _, _, _) => some root
            | .ok (none, _, _, _) => none
            | .error _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: dictionary construction failed"

private def dictSigned4Root : Cell :=
  mkDictFromPairs "SUBDICTIRPGET.dictSigned4Root" 4 #[
    (1, markerOne),
    (7, markerTwo),
    (-1, markerThree)
  ]

private def dictSigned0Root : Cell :=
  mkDictFromPairs "SUBDICTIRPGET.dictSigned0Root" 0 #[(0, markerFour)]

private def malformedDictCell : Cell := Cell.mkOrdinary (natToBits 0b10 2) #[]

private def expectedK0 : Array Value := #[(.cell dictSigned4Root)]
private def expectedK0Null : Array Value := #[.null]
private def expectedK2Hit : Array Value :=
  match dictExtractPrefixSubdictWithCells (some dictSigned4Root) 4 (requireBits "expectedK2Hit" 1 4) 2 true with
  | .ok (some c, _, _, _) => #[.cell c]
  | .ok (none, _, _, _) => #[.null]
  | .error e => panic! s!"expectedK2Hit: {reprStr e}"
private def expectedK2HitMinus1 : Array Value :=
  match dictExtractPrefixSubdictWithCells (some dictSigned4Root) 4 (requireBits "expectedK2HitMinus1" (-1) 4) 2 true with
  | .ok (some c, _, _, _) => #[.cell c]
  | .ok (none, _, _, _) => #[.null]
  | .error e => panic! s!"expectedK2HitMinus1: {reprStr e}"
private def expectedK4Hit : Array Value :=
  match dictExtractPrefixSubdictWithCells (some dictSigned4Root) 4 (requireBits "expectedK4Hit" 1 4) 4 true with
  | .ok (some c, _, _, _) => #[.cell c]
  | .ok (none, _, _, _) => #[.null]
  | .error e => panic! s!"expectedK4Hit: {reprStr e}"
private def expectedMiss : Array Value := #[.null]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def hitCreated : Nat :=
  match dictExtractPrefixSubdictWithCells (some dictSigned4Root) 4 (requireBits "hitCreated" 1 4) 2 true with
  | .ok (_, _, c, _) => c
  | .error _ => 0
private def hitGas : Int := baseGas + Int.ofNat hitCreated * cellCreateGasPrice
private def hitGasMinusOne : Int := if hitGas > 0 then hitGas - 1 else 0
private def baseGasExact : OracleGasLimits := oracleGasLimitsExact baseGas
private def baseGasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne
private def hitGasExact : OracleGasLimits := oracleGasLimitsExact hitGas
private def hitGasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne hitGasMinusOne

private def runSubdictIRPGET (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runSubdictIRPGETFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.dictGet false false false) (VM.push (intV dispatchSentinel)) stack

private def mkStack (key : Int) (dict : Value) (k : Int) (n : Int) : Array Value :=
  #[intV key, dict, intV k, intV n]

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

private def mkCaseCode
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

private def expectDecodeInvOpcode (label : String) (w16 : Nat) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 w16) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, _bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr}")

private def genSUBDICTIRPGET (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 34
  let (tag, _) := randNat rng1 0 999_999
  let (case0, rng3) :=
    if shape = 0 then
      (mkCase "ok/k0-root" (mkStack 1 (.cell dictSigned4Root) 0 4), rng1)
    else if shape = 1 then
      (mkCase "ok/k0-null" (mkStack 1 .null 0 4), rng1)
    else if shape = 2 then
      (mkCase "ok/k2-hit-1" (mkStack 1 (.cell dictSigned4Root) 2 4), rng1)
    else if shape = 3 then
      (mkCase "ok/k2-hit--1" (mkStack (-1) (.cell dictSigned4Root) 2 4), rng1)
    else if shape = 4 then
      (mkCase "ok/k4-hit" (mkStack 1 (.cell dictSigned4Root) 4 4), rng1)
    else if shape = 5 then
      (mkCase "ok/k2-miss" (mkStack (-8) (.cell dictSigned4Root) 2 4), rng1)
    else if shape = 6 then
      (mkCase "ok/n0" (mkStack 0 (.cell dictSigned0Root) 0 0), rng1)
    else if shape = 7 then
      (mkCase "err/underflow-0" #[], rng1)
    else if shape = 8 then
      (mkCase "err/underflow-1" #[intV 4], rng1)
    else if shape = 9 then
      (mkCase "err/underflow-2" (#[intV 1, .cell dictSigned4Root]), rng1)
    else if shape = 10 then
      (mkCase "err/underflow-3" (#[intV 1, .cell dictSigned4Root, intV 2]), rng1)
    else if shape = 11 then
      (mkCase "err/n-type" (#[intV 1, .cell dictSigned4Root, intV 1, .tuple #[]]), rng1)
    else if shape = 12 then
      (mkCase "err/n-negative" (mkStack 1 (.cell dictSigned4Root) 1 (-1)), rng1)
    else if shape = 13 then
      (mkCase "err/n-too-large" (mkStack 1 (.cell dictSigned4Root) 1 1024), rng1)
    else if shape = 14 then
      (mkCase "err/n-nan" (#[intV 1, .cell dictSigned4Root, intV 1, .int .nan]), rng1)
    else if shape = 15 then
      (mkCase "err/dict-builder" (mkStack 1 (.builder Builder.empty) 1 4), rng1)
    else if shape = 16 then
      (mkCase "err/dict-tuple" (#[intV 1, .tuple #[], intV 1, intV 4]), rng1)
    else if shape = 17 then
      (mkCase "err/k-type" (#[intV 1, .cell dictSigned4Root, .slice (mkSliceFromBits #[]), intV 4]), rng1)
    else if shape = 18 then
      (mkCase "err/k-negative" (mkStack 1 (.cell dictSigned4Root) (-1) 4), rng1)
    else if shape = 19 then
      (mkCase "err/k-over-n" (mkStack 1 (.cell dictSigned4Root) 5 4), rng1)
    else if shape = 20 then
      (mkCase "err/key-slice" (#[.slice (mkSliceFromBits #[]), .cell dictSigned4Root, intV 1, intV 4]), rng1)
    else if shape = 21 then
      (mkCase "err/key-cell" (#[.cell (Cell.empty), .cell dictSigned4Root, intV 1, intV 4]), rng1)
    else if shape = 22 then
      (mkCase "err/key-nan" (#[.int .nan, .cell dictSigned4Root, intV 1, intV 4]), rng1)
    else if shape = 23 then
      (mkCase "err/key-out-of-range-pos" (mkStack 8 (.cell dictSigned4Root) 4 4), rng1)
    else if shape = 24 then
      (mkCase "err/key-out-of-range-neg" (mkStack (-9) (.cell dictSigned4Root) 4 4), rng1)
    else if shape = 25 then
      (mkCase "err/key-out-of-range-k0" (mkStack 1 (.cell dictSigned4Root) 0 4), rng1)
    else if shape = 26 then
      (mkCase "err/malformed-dict" (mkStack 1 (.cell malformedDictCell) 4 4), rng1)
    else if shape = 27 then
      (mkCaseCode "decode/f4b5" #[] rawF4b5, rng1)
    else if shape = 28 then
      (mkCaseCode "decode/f4b6" #[] rawF4b6, rng1)
    else if shape = 29 then
      (mkCaseCode "decode/f4b7" #[] rawF4b7, rng1)
    else if shape = 30 then
      (mkCaseCode "decode/f4b4" #[] rawF4b4, rng1)
    else if shape = 31 then
      (mkCaseCode "decode/f4b8" #[] rawF4b8, rng1)
    else if shape = 32 then
      (mkCaseCode "decode/f4" #[] rawF4, rng1)
    else if shape = 33 then
      (mkCase "gas/exact/k0" (mkStack 1 (.cell dictSigned4Root) 0 4)
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
        baseGasExact, rng1)
    else if shape = 34 then
      (mkCase "gas/exact-hit" (mkStack 1 (.cell dictSigned4Root) 2 4)
        (#[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr])
        hitGasExact, rng1)
    else
      (mkCase "or/fallback-random" (mkStack 1 (.cell dictSigned4Root) 2 4), rng1)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let out := runSubdictIRPGETFallback #[]
        expectOkStack "fallback" out (#[] ++ #[(intV dispatchSentinel)]) },
    { name := "unit/underflow" -- [B2]
      run := do
        expectErr "underflow-0" (runSubdictIRPGET #[]) .stkUnd
        expectErr "underflow-1" (runSubdictIRPGET #[intV 4]) .stkUnd
        expectErr "underflow-2" (runSubdictIRPGET (#[intV 1, .cell dictSigned4Root])) .stkUnd
        expectErr "underflow-3" (runSubdictIRPGET (#[intV 1, .cell dictSigned4Root, intV 2])) .stkUnd },
    { name := "unit/validation/n" -- [B3]
      run := do
        expectErr "n-type" (runSubdictIRPGET (#[intV 1, .cell dictSigned4Root, intV 1, .tuple #[]])) .typeChk
        expectErr "n-negative" (runSubdictIRPGET (mkStack 1 (.cell dictSigned4Root) 1 (-1))) .rangeChk
        expectErr "n-too-large" (runSubdictIRPGET (mkStack 1 (.cell dictSigned4Root) 1 1024)) .rangeChk
        expectErr "n-nan" (runSubdictIRPGET (#[intV 1, .cell dictSigned4Root, intV 1, .int .nan])) .rangeChk },
    { name := "unit/validation/dict" -- [B4]
      run := do
        expectErr "dict-builder" (runSubdictIRPGET (mkStack 1 (.builder Builder.empty) 1 4)) .typeChk
        expectErr "dict-tuple" (runSubdictIRPGET (mkStack 1 (.tuple #[]) 1 4)) .typeChk },
    { name := "unit/validation/k" -- [B5]
      run := do
        expectErr "k-type" (runSubdictIRPGET (#[intV 1, .cell dictSigned4Root, .slice (mkSliceFromBits #[]), intV 4])) .typeChk
        expectErr "k-negative" (runSubdictIRPGET (mkStack 1 (.cell dictSigned4Root) (-1) 4)) .rangeChk
        expectErr "k-over-n" (runSubdictIRPGET (mkStack 1 (.cell dictSigned4Root) 5 4)) .rangeChk },
    { name := "unit/validation/key" -- [B6][B7]
      run := do
        expectErr "key-type" (runSubdictIRPGET (#[.slice (mkSliceFromBits #[]), .cell dictSigned4Root, intV 1, intV 4])) .typeChk
        expectErr "key-nan" (runSubdictIRPGET (#[.int .nan, .cell dictSigned4Root, intV 1, intV 4])) .intOv
        expectErr "key-out-of-range-pos" (runSubdictIRPGET (mkStack 8 (.cell dictSigned4Root) 4 4)) .dictErr
        expectErr "key-out-of-range-neg" (runSubdictIRPGET (mkStack (-9) (.cell dictSigned4Root) 4 4)) .dictErr
        expectErr "key-out-of-range-k0" (runSubdictIRPGET (mkStack 1 (.cell dictSigned4Root) 0 4)) .dictErr },
    { name := "unit/semantics/success" -- [B8][B9]
      run := do
        expectOkStack "k0-root" (runSubdictIRPGET (mkStack 1 (.cell dictSigned4Root) 0 4)) expectedK0
        expectOkStack "k0-null" (runSubdictIRPGET (mkStack 1 .null 0 4)) expectedK0Null
        expectOkStack "k0-n0" (runSubdictIRPGET (mkStack 0 (.cell dictSigned0Root) 0 0)) #[(.cell dictSigned0Root)]
        expectOkStack "k2-hit" (runSubdictIRPGET (mkStack 1 (.cell dictSigned4Root) 2 4)) expectedK2Hit
        expectOkStack "k2-hit-neg1" (runSubdictIRPGET (mkStack (-1) (.cell dictSigned4Root) 2 4)) expectedK2HitMinus1
        expectOkStack "k4-hit" (runSubdictIRPGET (mkStack 1 (.cell dictSigned4Root) 4 4)) expectedK4Hit
        expectOkStack "k2-miss" (runSubdictIRPGET (mkStack 4 (.cell dictSigned4Root) 2 4)) expectedMiss },
    { name := "unit/semantics/malformed" -- [B10][B7]
      run := do
        expectErr "malformed" (runSubdictIRPGET (mkStack 1 (.cell malformedDictCell) 4 4)) .dictErr },
    { name := "unit/assembler" -- [B10]
      run := do
        match assembleCp0 [instr] with
        | .error .invOpcode => pure ()
        | .ok _ => throw (IO.userError "assemble unexpectedly succeeded")
        | .error e => throw (IO.userError s!"assemble failed with {e}") },
    { name := "unit/decoder" -- [B11]
      run := do
        let _ ← expectDecodeStep "decode/f4b6" (opcodeSlice16 0xf4b6) (.dictExt (.subdictGet true false true)) 16
        let _ ← expectDecodeStep "decode/f4b5" (opcodeSlice16 0xf4b5) (.dictExt (.subdictGet false false true)) 16
        let _ ← expectDecodeStep "decode/f4b7" (opcodeSlice16 0xf4b7) (.dictExt (.subdictGet true true true)) 16
        expectDecodeInvOpcode "decode/f4b4" 0xf4b4
        expectDecodeInvOpcode "decode/f4b8" 0xf4b8
        expectDecodeInvOpcode "decode/f4" 0xf4 }
    ]
  oracle := #[
    mkCase "or/underflow-0" #[], -- [B2]
    mkCase "or/underflow-1" #[intV 4], -- [B2]
    mkCase "or/underflow-2" (#[intV 1, .cell dictSigned4Root]), -- [B2]
    mkCase "or/underflow-3" (#[intV 1, .cell dictSigned4Root, intV 2]), -- [B2]
    mkCase "or/n-type" (#[intV 1, .cell dictSigned4Root, intV 1, .tuple #[]]), -- [B3]
    mkCase "or/n-neg" (mkStack 1 (.cell dictSigned4Root) 1 (-1)), -- [B3]
    mkCase "or/n-too-large" (mkStack 1 (.cell dictSigned4Root) 1 1024), -- [B3]
    mkCase "or/n-nan" (#[intV 1, .cell dictSigned4Root, intV 1, .int .nan]), -- [B3]
    mkCase "or/dict-builder" (mkStack 1 (.builder Builder.empty) 1 4), -- [B4]
    mkCase "or/dict-tuple" (#[intV 1, .tuple #[], intV 1, intV 4]), -- [B4]
    mkCase "or/k-type" (#[intV 1, .cell dictSigned4Root, .slice (mkSliceFromBits #[]), intV 4]), -- [B5]
    mkCase "or/k-neg" (mkStack 1 (.cell dictSigned4Root) (-1) 4), -- [B5]
    mkCase "or/k-over-n" (mkStack 1 (.cell dictSigned4Root) 5 4), -- [B5]
    mkCase "or/key-slice" (#[.slice (mkSliceFromBits #[]), .cell dictSigned4Root, intV 1, intV 4]), -- [B6]
    mkCase "or/key-cell" (#[.cell (Cell.empty), .cell dictSigned4Root, intV 1, intV 4]), -- [B6]
    mkCase "or/key-nan" (#[.int .nan, .cell dictSigned4Root, intV 1, intV 4]), -- [B6]
    mkCase "or/key-oob-pos" (mkStack 8 (.cell dictSigned4Root) 4 4), -- [B7]
    mkCase "or/key-oob-neg" (mkStack (-9) (.cell dictSigned4Root) 4 4), -- [B7]
    mkCase "or/key-oob-k0" (mkStack 1 (.cell dictSigned4Root) 0 4), -- [B7]
    mkCase "or/success-k0-root" (mkStack 1 (.cell dictSigned4Root) 0 4), -- [B8][B9]
    mkCase "or/success-k0-null" (mkStack 1 .null 0 4), -- [B8][B9]
    mkCase "or/success-k2-hit-1" (mkStack 1 (.cell dictSigned4Root) 2 4), -- [B8][B9]
    mkCase "or/success-k2-hit--1" (mkStack (-1) (.cell dictSigned4Root) 2 4), -- [B8][B9]
    mkCase "or/success-k4-hit" (mkStack 1 (.cell dictSigned4Root) 4 4), -- [B8][B9]
    mkCase "or/miss-prefix" (mkStack 4 (.cell dictSigned4Root) 2 4), -- [B9]
    mkCase "or/miss-null-root" (mkStack 1 .null 2 4), -- [B9]
    mkCase "or/malformed" (mkStack 1 (.cell malformedDictCell) 4 4), -- [B10][B7]
    mkCaseCode "or/decode-f4b5" #[] rawF4b5, -- [B11]
    mkCaseCode "or/decode-f4b6" #[] rawF4b6, -- [B11]
    mkCaseCode "or/decode-f4b7" #[] rawF4b7, -- [B11]
    mkCaseCode "or/decode-f4b4" #[] rawF4b4, -- [B11]
    mkCaseCode "or/decode-f4b8" #[] rawF4b8, -- [B11]
    mkCaseCode "or/decode-truncated" #[] rawF4, -- [B11]
    mkCase "or/gas/exact-k0" (mkStack 1 (.cell dictSigned4Root) 0 4)
      #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]
      baseGasExact, -- [B12]
    mkCase "or/gas/exact-minus-one-k0" (mkStack 1 (.cell dictSigned4Root) 0 4)
      #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]
      baseGasExactMinusOne, -- [B12]
    mkCase "or/gas/exact-hit" (mkStack 1 (.cell dictSigned4Root) 2 4)
      #[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr]
      hitGasExact, -- [B12]
    mkCase "or/gas/exact-minus-one-hit" (mkStack 1 (.cell dictSigned4Root) 2 4)
      #[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr]
      hitGasExactMinusOne -- [B12]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genSUBDICTIRPGET } ]

initialize registerSuite suite

end Tests.Instr.Dict.SUBDICTIRPGET
