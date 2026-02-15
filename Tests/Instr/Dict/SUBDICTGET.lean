import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.SUBDICTGET

/-!
INSTRUCTION: SUBDICTGET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictDictGet` handles `.dictExt (.subdictGet ..)` and forwards any other
     instruction through `next`.

2. [B2] Stack underflow preconditions.
   - Exactly 4 operands are required: `n`, `dict`, `k`, `key` (or int key).

3. [B3] `n` validation.
   - `VM.popNatUpTo 1023` accepts only non-negative natural values in range.
   - `.typeChk` for non-int `n`.
   - `.rangeChk` for `.nan` and `n > 1023`.

4. [B4] Dictionary operand validation.
   - `VM.popMaybeCell` accepts only `null` or `cell`.
   - Non-cell/null dictionary values raise `.typeChk`.

5. [B5] Prefix-length (`k`) validation.
   - `k` is bounded by `min mk n`, where `mk = 257/1024` for signed/unsigned int variants and `1023` for slice.
   - `VM.popNatUpTo` performs the range/type checks for `k`.

6. [B6] Key-source path split (`slice` vs `int`).
   - Slice path requires stack key type `slice` and `haveBits k`.
   - Int path requires `popIntFinite`; `.intOv` / `.typeChk` surface on invalid int values.

7. [B7] Integer key extraction to bit key.
   - Signed (`unsigned = false`) and unsigned (`unsigned = true`) use different `dictKeyBits?` conversions.
   - Conversion miss (e.g. negative in unsigned mode, or out-of-range magnitude for given `k`) returns `cellUnd`.

8. [B8] Slice key length check.
   - If `slice` has fewer than `k` bits, `.cellUnd` is thrown.

9. [B9] Prefix extraction behavior.
   - On success with `n = null`, push `null`.
   - On success with match, push extracted sub-dictionary root (may be unchanged root for `k = 0`).
   - On prefix miss, push `null`.

10. [B10] Gas bookkeeping and precharge/load tracking.
    - `k = 0` skips explicit root-load precharge in Lean implementation.
    - `k > 0` calls `DictExt.prechargeRootLoad` and then consumes dynamic gas via `consumeCreatedGas` for
      dictionary-label rebuild operations.

11. [B11] Error remapping and structural errors.
    - `.dictErr` from `dictExtractPrefixSubdictWithCells` is rethrown for all modes.
    - A `cellUnd` from dictionary extraction is remapped to `dictErr` only for signed-int RP mode (`intKey = true`,
      `unsigned = false`, `rp = true`), matching implementation behavior.
    - Malformed dictionaries are expected to surface error behavior consistently with dictionary machinery.

12. [B12] Assembler encoding.
    - SUBDICTGET opcodes are encodable by CP0.
    - Assembly roundtrips through `decodeCp0WithBits` with 16-bit encoding.

13. [B13] Decoder behavior.
    - Valid opcodes are `0xf4b1..0xf4b3` (no RP) and `0xf4b5..0xf4b7` (RP).
    - Adjacent opcodes are invalid and must fail (`0xf4b0`, `0xf4b4`, `0xf4b8`).

14. [B14] Gas accounting.
    - Exact-gas-success and exact-gas-minus-one-failure branches are tested.
    - No separate opcode-level extra gas buckets are defined, but dynamic rebuild gas is consumed where applicable.

TOTAL BRANCHES: 14

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def subdictGetId : InstrId := { name := "SUBDICTGET" }

private def subdictSlice : Instr := .dictExt (.subdictGet false false false)
private def subdictSliceRP : Instr := .dictExt (.subdictGet false false true)
private def subdictInt : Instr := .dictExt (.subdictGet true false false)
private def subdictIntRP : Instr := .dictExt (.subdictGet true false true)
private def subdictUInt : Instr := .dictExt (.subdictGet true true false)
private def subdictUIntRP : Instr := .dictExt (.subdictGet true true true)

private def markerSlice (marker : Nat) : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits marker 16) #[])

private def markerSlice0 : Slice := markerSlice 0xa101
private def markerSlice4 : Slice := markerSlice 0xa104
private def markerSlice9 : Slice := markerSlice 0xa109
private def markerSlice15 : Slice := markerSlice 0xa10f
private def markerInt0 : Slice := markerSlice 0xb001
private def markerInt5 : Slice := markerSlice 0xb005
private def markerIntNeg1 : Slice := markerSlice 0xb0ff
private def markerUInt0 : Slice := markerSlice 0xc001
private def markerUInt5 : Slice := markerSlice 0xc005
private def markerUInt15 : Slice := markerSlice 0xc00f

private def mkDictFromBitPairs (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let keyBits : BitString := pair.1
      let value : Slice := pair.2
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some next, _, _, _) => root := some next
      | .ok (none, _, _, _) => panic! s!"{label}: dictionary set unexpectedly returned none"
      | .error e => panic! s!"{label}: dictionary set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: failed to build dictionary"

private def requireBits (label : String) (key : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? key n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: unsupported key {key} for n={n} unsigned={unsigned}"

private def mkDictFromPairs (label : String) (n : Nat) (unsigned : Bool) (pairs : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let k : Int := pair.1
      let value : Slice := pair.2
      let keyBits : BitString := requireBits label k n unsigned
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some next, _, _, _) => root := some next
      | .ok (none, _, _, _) => panic! s!"{label}: dictionary set unexpectedly returned none"
      | .error e => panic! s!"{label}: dictionary set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: failed to build dictionary"

private def dictSlice4Root : Cell :=
  mkDictFromBitPairs
    "dictSlice4Root"
    #[
      (natToBits 0 4, markerSlice0),
      (natToBits 4 4, markerSlice4),
      (natToBits 9 4, markerSlice9),
      (natToBits 15 4, markerSlice15)
    ]

private def dictInt4Root : Cell :=
  mkDictFromPairs "dictInt4Root" 4 false #[
    (0, markerInt0),
    (5, markerInt5),
    (-1, markerIntNeg1)
  ]

private def dictUInt4Root : Cell :=
  mkDictFromPairs "dictUInt4Root" 4 true #[
    (0, markerUInt0),
    (5, markerUInt5),
    (15, markerUInt15)
  ]

private def malformedDictCell : Cell := Cell.mkOrdinary (natToBits 0b10 2) #[]

private def subdictGetGas : Int := computeExactGasBudget subdictSlice
private def subdictGetGasMinusOne : Int := computeExactGasBudgetMinusOne subdictSlice

private def rawF4b1 : Cell := Cell.mkOrdinary (natToBits 0xf4b1 16) #[]
private def rawF4b2 : Cell := Cell.mkOrdinary (natToBits 0xf4b2 16) #[]
private def rawF4b3 : Cell := Cell.mkOrdinary (natToBits 0xf4b3 16) #[]
private def rawF4b5 : Cell := Cell.mkOrdinary (natToBits 0xf4b5 16) #[]
private def rawF4b6 : Cell := Cell.mkOrdinary (natToBits 0xf4b6 16) #[]
private def rawF4b7 : Cell := Cell.mkOrdinary (natToBits 0xf4b7 16) #[]
private def rawF4b0 : Cell := Cell.mkOrdinary (natToBits 0xf4b0 16) #[]
private def rawF4b4 : Cell := Cell.mkOrdinary (natToBits 0xf4b4 16) #[]
private def rawF4b8 : Cell := Cell.mkOrdinary (natToBits 0xf4b8 16) #[]
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

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected invOpcode, got bits {c.bits.size}")
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

private def runSubdict
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runSubdictDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV 12_345)) stack

private def stackSliceSubdict
    (keyBits : BitString)
    (dictValue : Value)
    (prefixLen n : Int) : Array Value :=
  #[.slice (mkSliceFromBits keyBits), intV prefixLen, dictValue, intV n]

private def stackIntSubdict
    (key : Int)
    (dictValue : Value)
    (prefixLen n : Int) : Array Value :=
  #[intV key, intV prefixLen, dictValue, intV n]

private def mkCase
    (name : String)
    (instr : Instr)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[instr]) : OracleCase :=
  { name := name
    instr := subdictGetId
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
    (_program : Array Instr := #[]) : OracleCase :=
  { name := name
    instr := subdictGetId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genSubdictGetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 34
  let (tag, rng2) := randNat rng1 0 999_999
  let base := s!"fuzz/{tag}/{shape}"
  let case0 :=
    if shape = 0 then
      mkCase (s!"{base}/slice-k0-hit") subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 0 4)
    else if shape = 1 then
      mkCase
        (s!"{base}/slice-k3-hit")
        subdictSlice
        (stackSliceSubdict (natToBits 2 3) (.cell dictSlice4Root) 3 4)
    else if shape = 2 then
      mkCase
        (s!"{base}/slice-k3-miss")
        subdictSlice
        (stackSliceSubdict (natToBits 0b001 3) (.cell dictSlice4Root) 3 4)
    else if shape = 3 then
      mkCase
        (s!"{base}/slice-null")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) .null 2 4)
    else if shape = 4 then
      mkCase
        (s!"{base}/slice-k4-short")
        subdictSlice
        (stackSliceSubdict (natToBits 0 2) (.cell dictSlice4Root) 4 4)
    else if shape = 5 then
      mkCase
        (s!"{base}/int-k0-hit")
        subdictInt
        (stackIntSubdict 5 (.cell dictInt4Root) 0 4)
    else if shape = 6 then
      mkCase
        (s!"{base}/int-k0-miss")
        subdictInt
        (stackIntSubdict 2 (.cell dictInt4Root) 0 4)
    else if shape = 7 then
      mkCase
        (s!"{base}/int-k0-miss-unsigned-root")
        subdictUInt
        (stackIntSubdict 10 (.cell dictUInt4Root) 0 4)
    else if shape = 8 then
      mkCase
        (s!"{base}/int-signed-out-range-positive")
        subdictInt
        (stackIntSubdict 8 (.cell dictInt4Root) 4 4)
    else if shape = 9 then
      mkCase
        (s!"{base}/int-signed-out-range-negative")
        subdictInt
        (stackIntSubdict (-9) (.cell dictInt4Root) 4 4)
    else if shape = 10 then
      mkCase
        (s!"{base}/int-unsigned-out-range-negative")
        subdictUInt
        (stackIntSubdict (-1) (.cell dictUInt4Root) 4 4)
    else if shape = 11 then
      mkCase
        (s!"{base}/int-nan")
        subdictInt
        (#[.int .nan, intV 4, .cell dictInt4Root, intV 4])
    else if shape = 12 then
      mkCase
        (s!"{base}/k-non-int")
        subdictSlice
        (#[.slice (mkSliceFromBits (natToBits 0 4)), .null, .cell dictSlice4Root, intV 4])
    else if shape = 13 then
      mkCase
        (s!"{base}/k-negative")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) (-1) 4)
    else if shape = 14 then
      mkCase
        (s!"{base}/k-too-large")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 5 4)
    else if shape = 15 then
      mkCase
        (s!"{base}/n-non-int")
        subdictSlice
        (#[.slice (mkSliceFromBits (natToBits 0 4)), intV 2, .cell dictSlice4Root, .null])
    else if shape = 16 then
      mkCase
        (s!"{base}/n-negative")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 2 (-1))
    else if shape = 17 then
      mkCase
        (s!"{base}/n-too-large")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 2 1024)
    else if shape = 18 then
      mkCase
        (s!"{base}/dict-builder")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.builder Builder.empty) 2 4)
    else if shape = 19 then
      mkCase
        (s!"{base}/dict-tuple")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.tuple #[]) 2 4)
    else if shape = 20 then
      mkCase
        (s!"{base}/key-slice-in-int-mode")
        subdictInt
        (#[.slice (mkSliceFromBits (natToBits 0 4)), intV 4, .cell dictInt4Root, intV 4])
    else if shape = 21 then
      mkCase
        (s!"{base}/key-rp")
        subdictSliceRP
        (stackSliceSubdict (natToBits 3 4) (.cell dictSlice4Root) 2 4)
    else if shape = 22 then
      mkCase
        (s!"{base}/key-rp-miss")
        subdictIntRP
        (stackIntSubdict 5 (.cell dictInt4Root) 4 4)
    else if shape = 23 then
      mkCase
        (s!"{base}/key-unsigned-rp")
        subdictUIntRP
        (stackIntSubdict 15 (.cell dictUInt4Root) 4 4)
    else if shape = 24 then
      mkCase
        (s!"{base}/malformed-root")
        subdictInt
        (stackIntSubdict 1 (.cell malformedDictCell) 4 4)
    else if shape = 25 then
      mkCase
        (s!"{base}/malformed-root-rp")
        subdictIntRP
        (stackIntSubdict 1 (.cell malformedDictCell) 4 4)
    else if shape = 26 then
      mkCase
        (s!"{base}/decode/raw/f4b1")
        subdictSlice
        (#[])
        (gasLimits := {})
        (program := #[subdictSlice])
        |> fun _ => mkCaseCode (s!"{base}/decode/raw/f4b1") #[] rawF4b1
    else if shape = 27 then
      mkCase
        (s!"{base}/decode/raw/f4b6")
        subdictInt
        (#[])
        (program := #[subdictInt])
        |> fun _ => mkCaseCode (s!"{base}/decode/raw/f4b6") #[] rawF4b6
    else if shape = 28 then
      mkCase
        (s!"{base}/gas/exact")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 0 4)
        (gasLimits := oracleGasLimitsExact subdictGetGas)
        (program := #[.pushInt (.num subdictGetGas), .tonEnvOp .setGasLimit, subdictSlice])
    else if shape = 29 then
      mkCase
        (s!"{base}/gas/exact-minus-one")
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 0 4)
        (gasLimits := oracleGasLimitsExactMinusOne subdictGetGas)
        (program := #[.pushInt (.num subdictGetGasMinusOne), .tonEnvOp .setGasLimit, subdictSlice])
    else if shape = 30 then
      mkCase
        (s!"{base}/raw/invalid/0xf4b0")
        subdictSlice
        #[]
        (program := #[subdictSlice])
        |> fun _ => mkCaseCode (s!"{base}/raw/invalid/0xf4b0") #[] rawF4b0
    else if shape = 31 then
      mkCase
        (s!"{base}/raw/invalid/0xf4b4")
        subdictSlice
        #[]
        (program := #[subdictSlice])
        |> fun _ => mkCaseCode (s!"{base}/raw/invalid/0xf4b4") #[] rawF4b4
    else if shape = 32 then
      mkCase
        (s!"{base}/raw/invalid/0xf4b8")
        subdictSlice
        #[]
        (program := #[subdictSlice])
        |> fun _ => mkCaseCode (s!"{base}/raw/invalid/0xf4b8") #[] rawF4b8
    else
      mkCaseCode
        (s!"{base}/raw/truncated8")
        #[]
        rawF4
  (case0, rng2)

  def suite : InstrSuite where
    id := subdictGetId
    unit := #[
      { name := "unit/dispatch/match-vs-fallback" -- [B1]
        run := do
          let sentinel : Int := 12_345
          expectOkStack
            "fallback/non-match"
            (runSubdictDispatchFallback .add #[])
            (#[intV sentinel])
          expectOkStack
            "match/subdict"
            (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 0 4))
            (#[.cell dictSlice4Root]) },
      { name := "unit/underflow" -- [B2]
        run := do
          expectErr "empty-stack" (runSubdict subdictSlice #[]) .stkUnd
          expectErr "one-item" (runSubdict subdictSlice #[.slice (mkSliceFromBits (natToBits 0 4))]) .stkUnd
          expectErr "two-items" (runSubdict subdictSlice (#[.slice (mkSliceFromBits (natToBits 0 4)), .cell dictSlice4Root])) .stkUnd
          expectErr "three-items" (runSubdict subdictSlice (#[.slice (mkSliceFromBits (natToBits 0 4)), .cell dictSlice4Root, intV 4]) ) .stkUnd },
      { name := "unit/n-validation" -- [B3]
        run := do
          expectErr "n-not-int" (runSubdict subdictSlice (#[.slice (mkSliceFromBits (natToBits 0 4)), intV 1, .cell dictSlice4Root, .null])) .typeChk
          expectErr "n-negative" (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 4 (-1))) .rangeChk
          expectErr "n-too-large" (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 4 1024)) .rangeChk
          expectErr "n-nan" (runSubdict subdictSlice (#[.slice (mkSliceFromBits (natToBits 0 4)), intV 4, .cell dictSlice4Root, .int .nan])) .rangeChk },
      { name := "unit/k-validation" -- [B5]
        run := do
          expectErr "k-not-int" (runSubdict subdictSlice (#[.slice (mkSliceFromBits (natToBits 0 4)), .null, .cell dictSlice4Root, intV 4])) .typeChk
          expectErr "k-negative" (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) (-1) 4)) .rangeChk
          expectErr "k-too-large" (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 5 4)) .rangeChk },
      { name := "unit/type-checks" -- [B4][B6]
        run := do
          expectErr "dict-not-null-or-cell" (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 4) (.tuple #[]) 2 4)) .typeChk
          expectErr "dict-builder" (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 4) (.builder Builder.empty) 2 4)) .typeChk
          expectErr "slice-key-in-int" (runSubdict subdictInt (#[.slice (mkSliceFromBits (natToBits 0 4)), intV 4, .cell dictInt4Root, intV 4])) .typeChk
          expectErr "int-key-in-slice" (runSubdict subdictSlice (#[intV 5, intV 4, .cell dictSlice4Root, intV 4])) .typeChk },
      { name := "unit/key-conversion-errors" -- [B7][B8]
        run := do
          expectErr "slice-key-too-short" (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 2) (.cell dictSlice4Root) 4 4)) .cellUnd
          expectErr "int-key-out-of-range-pos" (runSubdict subdictInt (stackIntSubdict 8 (.cell dictInt4Root) 4 4)) .cellUnd
          expectErr "int-key-out-of-range-neg" (runSubdict subdictInt (stackIntSubdict (-9) (.cell dictInt4Root) 4 4)) .cellUnd
          expectErr "uint-key-out-of-range-neg" (runSubdict subdictUInt (stackIntSubdict (-1) (.cell dictUInt4Root) 4 4)) .cellUnd
          expectErr "int-nan" (runSubdict subdictInt (#[.int .nan, intV 4, .cell dictInt4Root, intV 4])) .intOv },
      { name := "unit/success/path-k0" -- [B9]
        run := do
          expectOkStack "slice-k0-hit" (runSubdict subdictSlice (stackSliceSubdict (natToBits 1 4) (.cell dictSlice4Root) 0 4)) (#[.cell dictSlice4Root])
          expectOkStack "int-k0-hit" (runSubdict subdictInt (stackIntSubdict 0 (.cell dictInt4Root) 0 4)) (#[.cell dictInt4Root])
          expectOkStack "uint-k0-hit" (runSubdict subdictUInt (stackIntSubdict 0 (.cell dictUInt4Root) 0 4)) (#[.cell dictUInt4Root])
          expectOkStack
            "slice-k0-preserve"
            (runSubdict subdictSlice
              #[intV 77, .slice (mkSliceFromBits (natToBits 2 3)), intV 0, .cell dictSlice4Root, intV 4])
            (#[intV 77, .cell dictSlice4Root])
      },
      { name := "unit/semantics-miss" -- [B9][B10]
        run := do
          expectOkStack
            "slice-prefix-miss"
            (runSubdict subdictSlice (stackSliceSubdict (natToBits 0b001 3) (.cell dictSlice4Root) 3 4))
            (#[.null])
          expectOkStack
            "slice-no-root"
            (runSubdict subdictSlice (stackSliceSubdict (natToBits 0 4) .null 2 4))
            (#[.null])
          expectOkStack
            "int-prefix-miss"
            (runSubdict subdictInt (stackIntSubdict 2 (.cell dictInt4Root) 4 4))
            (#[.null]) },
      { name := "unit/structural-errors" -- [B11]
        run := do
          expectErr "malformed-root" (runSubdict subdictInt (stackIntSubdict 5 (.cell malformedDictCell) 4 4)) .cellUnd },
      { name := "unit/assembler-roundtrip" -- [B12]
        run := do
          expectAssembleExact "encode/slice" subdictSlice 0xf4b1
          expectAssembleExact "encode/int-signed" subdictInt 0xf4b2
          expectAssembleExact "encode/uint" subdictUInt 0xf4b3
          expectAssembleExact "encode/slice-rp" subdictSliceRP 0xf4b5
          expectAssembleExact "encode/int-signed-rp" subdictIntRP 0xf4b6
          expectAssembleExact "encode/uint-rp" subdictUIntRP 0xf4b7 },
      { name := "unit/decoder-paths" -- [B13]
        run := do
          let _ ← expectDecodeStep "decode/f4b1" (opcodeSlice16 0xf4b1) (.dictExt (.subdictGet false false false)) 16
          let _ ← expectDecodeStep "decode/f4b2" (opcodeSlice16 0xf4b2) (.dictExt (.subdictGet true false false)) 16
          let _ ← expectDecodeStep "decode/f4b3" (opcodeSlice16 0xf4b3) (.dictExt (.subdictGet true true false)) 16
          let _ ← expectDecodeStep "decode/f4b5" (opcodeSlice16 0xf4b5) (.dictExt (.subdictGet false false true)) 16
          let _ ← expectDecodeStep "decode/f4b6" (opcodeSlice16 0xf4b6) (.dictExt (.subdictGet true false true)) 16
          let _ ← expectDecodeStep "decode/f4b7" (opcodeSlice16 0xf4b7) (.dictExt (.subdictGet true true true)) 16
          expectDecodeInvOpcode "decode/invalid/f4b0" 0xf4b0
          expectDecodeInvOpcode "decode/invalid/f4b4" 0xf4b4
          expectDecodeInvOpcode "decode/invalid/f4b8" 0xf4b8
          match decodeCp0WithBits (Slice.ofCell rawF4) with
          | .error _ => pure ()
          | .ok _ => throw (IO.userError "decode/truncated-8bit expected failure") } ]
    oracle := #[
      -- [B2]
      mkCase "or/underflow-empty" subdictSlice #[],
      mkCase "or/underflow-one" subdictSlice #[.slice (mkSliceFromBits (natToBits 0 4))],
      mkCase "or/underflow-two" subdictSlice #[.slice (mkSliceFromBits (natToBits 0 4)), .cell dictSlice4Root],
      mkCase "or/underflow-three" subdictSlice #[.slice (mkSliceFromBits (natToBits 0 4)), .cell dictSlice4Root, intV 4],
      mkCase "or/underflow-four" subdictSlice #[.slice (mkSliceFromBits (natToBits 0 4)), .cell dictSlice4Root, intV 4, .int (.num 5)],
      -- [B3]
      mkCase "or/n-type" subdictSlice #[.slice (mkSliceFromBits (natToBits 0 4)), intV 4, .cell dictSlice4Root, .tuple #[]],
      mkCase "or/n-negative" subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 4 (-1)),
      mkCase "or/n-too-large" subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 4 1024),
      mkCase "or/n-nan" subdictSlice (#[.slice (mkSliceFromBits (natToBits 0 4)), intV 4, .cell dictSlice4Root, .int .nan]),
      -- [B4]
      mkCase "or/dict-builder" subdictSlice (stackSliceSubdict (natToBits 0 4) (.builder Builder.empty) 2 4),
      mkCase "or/dict-tuple" subdictSlice (stackSliceSubdict (natToBits 0 4) (.tuple #[]) 2 4),
      -- [B5]
      mkCase "or/k-type" subdictSlice (#[.slice (mkSliceFromBits (natToBits 0 4)), .null, .cell dictSlice4Root, intV 4]),
      mkCase "or/k-negative" subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) (-1) 4),
      mkCase "or/k-too-large" subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 5 4),
      -- [B6][B7][B8]
      mkCase "or/key-type-slice-for-int" subdictInt (#[.slice (mkSliceFromBits (natToBits 0 4)), intV 4, .cell dictInt4Root, intV 4]),
      mkCase "or/int-key-nan" subdictInt (#[.int .nan, intV 4, .cell dictInt4Root, intV 4]),
      mkCase "or/int-key-signed-oob-pos" subdictInt (stackIntSubdict 8 (.cell dictInt4Root) 4 4),
      mkCase "or/int-key-signed-oob-neg" subdictInt (stackIntSubdict (-9) (.cell dictInt4Root) 4 4),
      mkCase "or/int-key-unsigned-neg" subdictUInt (stackIntSubdict (-1) (.cell dictUInt4Root) 4 4),
      mkCase "or/slice-key-short" subdictSlice (stackSliceSubdict (natToBits 0 3) (.cell dictSlice4Root) 4 4),
      -- [B9]
      mkCase "or/miss-prefix-slice" subdictSlice (stackSliceSubdict (natToBits 0b001 3) (.cell dictSlice4Root) 3 4),
      mkCase "or/miss-prefix-int" subdictInt (stackIntSubdict 2 (.cell dictInt4Root) 4 4),
      mkCase "or/miss-no-root" subdictSlice (stackSliceSubdict (natToBits 0 4) .null 4 4),
      mkCase "or/hit-k0-slice" subdictSlice (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 0 4),
      mkCase "or/hit-k0-int" subdictInt (stackIntSubdict 0 (.cell dictInt4Root) 0 4),
      mkCase "or/hit-k0-uint" subdictUInt (stackIntSubdict 15 (.cell dictUInt4Root) 0 4),
      mkCase "or/rp-int-hit" subdictIntRP (stackIntSubdict 5 (.cell dictInt4Root) 0 4),
      -- [B11]
      mkCase "or/match-prefix-slice-rp" subdictSliceRP (stackSliceSubdict (natToBits 2 3) (.cell dictSlice4Root) 3 4),
      mkCase "or/match-prefix-uint-rp" subdictUIntRP (stackIntSubdict 5 (.cell dictUInt4Root) 4 4),
      -- [B13]
      mkCaseCode "or/raw/f4b1" #[] rawF4b1,
      mkCaseCode "or/raw/f4b2" #[] rawF4b2,
      mkCaseCode "or/raw/f4b3" #[] rawF4b3,
      mkCaseCode "or/raw/f4b5" #[] rawF4b5,
      mkCaseCode "or/raw/f4b6" #[] rawF4b6,
      mkCaseCode "or/raw/f4b7" #[] rawF4b7,
      mkCaseCode "or/raw/invalid-0xf4b0" #[] rawF4b0,
      mkCaseCode "or/raw/invalid-0xf4b4" #[] rawF4b4,
      mkCaseCode "or/raw/invalid-0xf4b8" #[] rawF4b8,
      mkCaseCode "or/raw/truncated-8bit" #[] rawF4,
      -- [B11][B14]
      mkCase
        "or/structural-malformed" subdictInt (stackIntSubdict 0 (.cell malformedDictCell) 4 4),
      mkCase
        "or/gas/exact"
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 0 4)
        (oracleGasLimitsExact subdictGetGas)
        (program := #[.pushInt (.num subdictGetGas), .tonEnvOp .setGasLimit, subdictSlice]),
      mkCase
        "or/gas/exact-minus-one"
        subdictSlice
        (stackSliceSubdict (natToBits 0 4) (.cell dictSlice4Root) 0 4)
        (oracleGasLimitsExactMinusOne subdictGetGas)
        (program := #[.pushInt (.num subdictGetGasMinusOne), .tonEnvOp .setGasLimit, subdictSlice]) ]
    fuzz := #[
      { seed := fuzzSeedForInstr subdictGetId
        count := 500
        gen := genSubdictGetFuzzCase }
    ]

initialize registerSuite suite

end Tests.Instr.Dict.SUBDICTGET
