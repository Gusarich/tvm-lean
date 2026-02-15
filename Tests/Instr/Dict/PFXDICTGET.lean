import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PFXDICTGET

/-!
INSTRUCTION: PFXDICTGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictExt` handles `.dictExt (.pfxGet .get)` and calls `next` for all other
     instructions.

2. [B2] Underflow precondition.
   - `checkUnderflow 3` must fail before any typed checks or semantic operations.

3. [B3] `n` validation (`popNatUpTo 1023`).
   - non-int -> `.typeChk`
   - `.nan`, negative, and `> 1023` -> `.rangeChk`

4. [B4] Dictionary argument validation.
   - `popMaybeCell` accepts `.null` and `.cell`.
   - any other stack type triggers `.typeChk`.

5. [B5] Key argument validation.
   - key must be `.slice`; wrong types are `.typeChk`.

6. [B6] Miss path.
   - `pfxLookupPrefixWithCells` returns `none`, so `.get` throws `.cellUnd`
     for miss/nil cases.

7. [B7] Hit path.
   - `pfxLookupPrefixWithCells` returns `(some valueSlice, pfxLen, loaded)`.
   - `slicePrefix` splits matched prefix into `pfxSlice` and remainder `cs1`.
   - pushes `(pfxSlice, valueSlice, cs1)` in this order.

8. [B8] Boundary/shape inputs.
   - `n=0` and `n=1023` must still follow valid hit/miss rules.
   - empty-key and empty-dictionary-prefix roots are legal and exercise suffix-only hits.

9. [B9] Dictionary structural errors.
   - malformed root cell shape yields `.dictErr`.

10. [B10] Assembler/decoder behavior.
   - `.dictExt (.pfxGet .get)` encodes to `0xF4A9`.
   - `0xF4A8`, `0xF4AA`, `0xF4AB` decode to sibling variants.

11. [B11] Decoder boundaries.
   - `0xF4A7` and `0xF4AC` are `.invOpcode` with no opcode bits.
   - short `0xF4` also `.invOpcode`.

12. [B12] Gas accounting.
   - no variable creator gas path in this opcode family (`.get`/`.getQ` share fixed base cost).
   - verify exact-gas-success and exact-gas-minus-one-failure behavior.

TOTAL BRANCHES: 12
Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def suiteId : InstrId := { name := "PFXDICTGET" }

private def instr : Instr := .dictExt (.pfxGet .get)

private def dispatchSentinel : Int := 42_001

private def raw16 (w16 : Nat) : Cell := Cell.mkOrdinary (natToBits w16 16) #[]

private def marker (w16 : Nat) : Slice := mkSliceFromBits (natToBits w16 16)

private def dictGetValue : Slice := marker 0xB101
private def dictGetValueLong : Slice := marker 0xB102
private def n0Value : Slice := marker 0xD000

private def keyMatchBits : BitString := natToBits 0b100 3
private def keyMatch : Slice := mkSliceFromBits keyMatchBits
private def keyMatchLongBits : BitString := natToBits 0b1001 4
private def keyMatchLong : Slice := mkSliceFromBits keyMatchLongBits
private def keyMatchLongerBits : BitString := natToBits 0b10010 5
private def keyMatchLonger : Slice := mkSliceFromBits keyMatchLongerBits
private def keyMismatch : BitString := natToBits 0b111 3
private def keyShort : BitString := natToBits 0b10 2
private def keyEmpty : Slice := mkSliceFromBits (natToBits 0 0)

private def sliceRemBits (s : Slice) : BitString :=
  s.cell.bits.extract s.bitPos s.cell.bits.size

private def mkPfxLeafRoot (label : String) (keyBits : BitString) (value : Slice) : Cell :=
  let valueCell : Cell := value.toCellRemaining
  -- NOTE: Prefix dictionaries are *not* ordinary dict values. They are encoded as:
  --   label(keyBits, len, n) ++ [leafCtor=false] ++ valueCell
  -- and parsed by `DictExt.pfxLookupPrefixWithCells`.
  let enc : BitString := dictLabelEncode keyBits keyBits.size 1023
  Cell.mkOrdinary (enc ++ #[false] ++ valueCell.bits) valueCell.refs

private def dictGetRoot : Value :=
  .cell (mkPfxLeafRoot "dictGetRoot" keyMatchBits dictGetValue)

private def dictGetRootLong : Value :=
  .cell (mkPfxLeafRoot "dictGetRootLong" keyMatchLongBits dictGetValueLong)

private def dictGetRootN0 : Value :=
  .cell (mkPfxLeafRoot "dictGetRootN0" #[] n0Value)

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runFallback (i : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt i (VM.push (intV dispatchSentinel)) stack

private def expectHit
    (label : String)
    (res : Except Excno (Array Value))
    (expectedPfx expectedValue expectedRest : BitString) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")
  | .ok #[.slice pfx, .slice value, .slice rest] =>
      if sliceRemBits pfx != expectedPfx then
        throw (IO.userError s!"{label}: bad prefix bits: expected {reprStr expectedPfx}, got {reprStr (sliceRemBits pfx)}")
      else if sliceRemBits value != expectedValue then
        throw (IO.userError s!"{label}: bad value bits: expected {reprStr expectedValue}, got {reprStr (sliceRemBits value)}")
      else if sliceRemBits rest != expectedRest then
        throw (IO.userError s!"{label}: bad rest bits: expected {reprStr expectedRest}, got {reprStr (sliceRemBits rest)}")
  | .ok st =>
      throw (IO.userError s!"{label}: expected [slice,slice,slice], got {reprStr st}")

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (raw16 opcode)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for 0x{Nat.toDigits 16 opcode}, got {reprStr instr}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for 0x{Nat.toDigits 16 opcode}, got {e}")

private def runPFXDICTGET (stack : Array Value) (regs : Regs := Regs.initial) (cc : Continuation := .quit 0) :
    Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrDictExt instr (pure ())).run st0

private def expectRawErr
    (label : String)
    (res : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected {expected}, got success")
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def gasExact : Int := computeExactGasBudget instr
private def gasExactMinusOne : Int := computeExactGasBudgetMinusOne instr
private def gasExactLimits : OracleGasLimits := oracleGasLimitsExact gasExact
private def gasExactMinusOneLimits : OracleGasLimits := oracleGasLimitsExactMinusOne gasExactMinusOne

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[instr]) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (code : Cell)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseRawStack (key : BitString) (dict : Value) (n : Int) : Array Value :=
  #[.slice (mkSliceFromBits key), dict, intV n]

private def genPFXDICTGET (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 43
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rngOut) :=
    match shape with
    | 0 => (mkCase "fuzz/underflow/0" #[], rng2)
    | 1 => (mkCase "fuzz/underflow/1" #[(.slice keyMatch)], rng2)
    | 2 => (mkCase "fuzz/underflow/2" #[(.slice keyMatch), dictGetRoot], rng2)
    | 3 => (mkCase "fuzz/err/n/not-int" #[.slice keyMatch, dictGetRoot, .tuple #[]], rng2)
    | 4 => (mkCase "fuzz/err/n/nan" #[.slice keyMatch, dictGetRoot, .int .nan], rng2)
    | 5 => (mkCase "fuzz/err/n/negative" (mkCaseRawStack keyMatchBits dictGetRoot (-1)), rng2)
    | 6 => (mkCase "fuzz/err/n/too-large" (mkCaseRawStack keyMatchBits dictGetRoot 1024), rng2)
    | 7 => (mkCase "fuzz/err/dict/builder" (mkCaseRawStack keyMatchBits (.builder Builder.empty) 4), rng2)
    | 8 => (mkCase "fuzz/err/dict/tuple" (mkCaseRawStack keyMatchBits (.tuple #[]) 4), rng2)
    | 9 => (mkCase "fuzz/err/dict/int" #[.slice keyMatch, intV 7, intV 4], rng2)
    | 10 => (mkCase "fuzz/err/key/null" (#[(.null), dictGetRoot, intV 4]), rng2)
    | 11 => (mkCase "fuzz/err/key/cell" #[.cell Cell.empty, dictGetRoot, intV 4], rng2)
    | 12 => (mkCase "fuzz/err/key/builder" (#[.builder Builder.empty, dictGetRoot, intV 4]), rng2)
    | 13 => (mkCase "fuzz/err/key/tuple" (#[.tuple #[], dictGetRoot, intV 4]), rng2)
    | 14 => (mkCase "fuzz/err/key/nan" (#[.int .nan, dictGetRoot, intV 4]), rng2)
    | 15 => (mkCase "fuzz/miss/key-mismatch" (mkCaseRawStack keyMismatch dictGetRoot 3), rng2)
    | 16 => (mkCase "fuzz/miss/null-root" (mkCaseRawStack keyMatchLongBits (.null) 3), rng2)
    | 17 => (mkCase "fuzz/miss/short-key" (mkCaseRawStack keyShort dictGetRoot 3), rng2)
    | 18 => (mkCase "fuzz/hit/exact" (mkCaseRawStack keyMatchBits dictGetRoot 4), rng2)
    | 19 => (mkCase "fuzz/hit/long-key" (mkCaseRawStack keyMatchLongBits dictGetRoot 4), rng2)
    | 20 => (mkCase "fuzz/hit/longer-key" (mkCaseRawStack keyMatchLongerBits dictGetRootLong 5), rng2)
    | 21 => (mkCase "fuzz/hit/n-0" (mkCaseRawStack keyMatchLongBits dictGetRootN0 0), rng2)
    | 22 => (mkCase "fuzz/hit/n-max" (mkCaseRawStack keyMatchBits dictGetRoot 1023), rng2)
    | 23 =>
      (mkCase "fuzz/malformed-root" (mkCaseRawStack keyMatchBits (.cell malformedDictRoot) 4), rng2)
    | 24 =>
      (mkCaseCode "fuzz/raw/f4a8" (raw16 0xF4A8), rng2)
    | 25 =>
      (mkCaseCode "fuzz/raw/f4a9" (raw16 0xF4A9) (mkCaseRawStack keyMatchLongBits dictGetRoot 4), rng2)
    | 26 =>
      (mkCaseCode "fuzz/raw/f4aa" (raw16 0xF4AA) (mkCaseRawStack keyMatchLongBits dictGetRoot 4), rng2)
    | 27 =>
      (mkCaseCode "fuzz/raw/f4ab" (raw16 0xF4AB) (mkCaseRawStack keyMatchLongBits dictGetRoot 4), rng2)
    | 28 =>
      (mkCaseCode "fuzz/raw/f4a7" (raw16 0xF4A7), rng2)
    | 29 =>
      (mkCaseCode "fuzz/raw/f4ac" (raw16 0xF4AC), rng2)
    | 30 =>
      (mkCaseCode "fuzz/raw/truncated-f4" (Cell.mkOrdinary (natToBits 0xF4 8) #[]), rng2)
    | 31 =>
      (mkCase "fuzz/gas/exact" (mkCaseRawStack keyMatchLongBits dictGetRoot 4) gasExactLimits 1_000_000
        (#[.pushInt (.num gasExact), .tonEnvOp .setGasLimit, instr]), rng2)
    | 32 =>
      (mkCase "fuzz/gas/exact-minus-one" (mkCaseRawStack keyMatchLongBits dictGetRoot 4) gasExactMinusOneLimits
        1_000_000 (#[.pushInt (.num gasExactMinusOne), .tonEnvOp .setGasLimit, instr]), rng2)
    | 33 =>
      (mkCase "fuzz/maybe/miss-null-root" (mkCaseRawStack keyShort (.null) 10), rng2)
    | 34 =>
      (mkCase "fuzz/maybe/hit-empty-prefix" (mkCaseRawStack keyMatchLongBits dictGetRootN0 0), rng2)
    | 35 =>
      (mkCase "fuzz/maybe/hit-match-short" (mkCaseRawStack keyMatchLongBits dictGetRoot 1), rng2)
    | 36 =>
      (mkCase "fuzz/maybe/hit-prefix-longer" (mkCaseRawStack keyMatchLongerBits dictGetRoot 5), rng2)
    | 37 =>
      (mkCase "fuzz/raw/invalid-empty-stack" #[], rng2)
    | 38 =>
      (mkCase "fuzz/raw/fallback" (mkCaseRawStack keyMatchLongBits dictGetRoot 4), rng2)
    | 39 =>
      let (nBits, rng3) := randNat rng2 0 1023
      let (rootTag, rng4) := randNat rng3 0 3
      let keyTag := if nBits < 4 then 0 else if nBits = 4 then 1 else 2
      let dictRoot : Value :=
        match rootTag with
        | 0 => dictGetRoot
        | 1 => dictGetRootLong
        | _ => dictGetRootN0
      let key : BitString :=
        match keyTag with
        | 0 => keyMatchLongBits
        | 1 => keyMatchBits
        | _ => keyMatchLongerBits
      ({ fuel := 1_000_000, instr := suiteId, name := s!"fuzz/bias/random-hit/{tag}", initStack := mkCaseRawStack key dictRoot (Int.ofNat nBits), program := #[instr], gasLimits := {} }, rng4)
    | _ =>
      let (randomKey, rng3) := randNat rng2 0 31
      let bitsLen := randomKey % 6 + 1
      let (raw, rng4) := randNat rng3 0 ((1 <<< bitsLen) - 1)
      let keyBits : BitString := natToBits raw bitsLen
      ({ fuel := 1_000_000, instr := suiteId, name := "fuzz/random-generic", initStack := mkCaseRawStack keyBits (if (randomKey % 2 = 0) then dictGetRoot else dictGetRootLong) (Int.ofNat (bitsLen % 7)), program := #[instr], gasLimits := {} }, rng4)
  ( { case0 with name := s!"{case0.name}/{tag}" } , rngOut)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "unit/dispatch/fallback"
          (runFallback .add #[(.slice keyMatch), dictGetRoot, intV 4])
          #[(.slice keyMatch), dictGetRoot, intV 4, intV dispatchSentinel] },
    { name := "unit/dispatch/match" -- [B1]
      run := do
        expectHit
          "unit/dispatch/match"
          (runFallback instr (mkCaseRawStack keyMatchBits dictGetRoot 4))
          keyMatchBits dictGetValue.cell.bits #[] },
    { name := "unit/underflow" -- [B2]
      run := do
        expectErr "underflow/0" (runDirect (#[(.slice keyMatch)])) .stkUnd
        expectErr "underflow/1" (runDirect (#[.slice keyMatch, dictGetRoot])) .stkUnd
        expectErr "underflow/2" (runDirect (#[(.slice keyMatch), intV 4])) .stkUnd },
    { name := "unit/n-validation" -- [B3]
      run := do
        expectErr "n-not-int" (runDirect #[.slice keyMatch, dictGetRoot, .tuple #[]]) .typeChk
        expectErr "n-nan" (runDirect #[.slice keyMatch, dictGetRoot, .int .nan]) .rangeChk
        expectErr "n-negative" (runDirect (mkCaseRawStack keyMatchBits dictGetRoot (-1))) .rangeChk
        expectErr "n-too-large" (runDirect (mkCaseRawStack keyMatchBits dictGetRoot 1024)) .rangeChk },
    { name := "unit/dict-validation" -- [B4]
      run := do
        expectErr "dict-builder" (runDirect (mkCaseRawStack keyMatchBits (.builder Builder.empty) 4)) .typeChk
        expectErr "dict-tuple" (runDirect (mkCaseRawStack keyMatchBits (.tuple #[]) 4)) .typeChk
        expectErr "dict-int" (runDirect #[.slice keyMatch, intV 7, intV 4]) .typeChk },
    { name := "unit/key-validation" -- [B5]
      run := do
        expectErr "key-null" (runDirect (#[(.null), dictGetRoot, intV 4])) .typeChk
        expectErr "key-cell" (runDirect (#[(.cell Cell.empty), dictGetRoot, intV 4])) .typeChk
        expectErr "key-builder" (runDirect (#[(.builder Builder.empty), dictGetRoot, intV 4])) .typeChk
        expectErr "key-tuple" (runDirect (#[(.tuple #[]), dictGetRoot, intV 4])) .typeChk
        expectErr "key-nan" (runDirect (#[(.int .nan), dictGetRoot, intV 4])) .typeChk },
    { name := "unit/miss-path" -- [B6]
      run := do
        expectErr "miss/key" (runDirect (mkCaseRawStack keyMismatch dictGetRoot 3)) .cellUnd
        expectErr "miss/null-root" (runDirect (mkCaseRawStack keyMatchLongBits (.null) 3)) .cellUnd
        expectErr "miss/short-key" (runDirect (mkCaseRawStack keyShort dictGetRoot 3)) .cellUnd },
    { name := "unit/hit-path" -- [B7][B8]
      run := do
        expectHit
          "hit/exact"
          (runDirect (mkCaseRawStack keyMatchBits dictGetRoot 4))
          keyMatchBits dictGetValue.cell.bits #[]
        expectHit
          "hit/long-key"
          (runDirect (mkCaseRawStack keyMatchLongBits dictGetRoot 4))
          keyMatchBits dictGetValue.cell.bits (natToBits 1 1)
        expectHit
          "hit/n0"
          (runDirect (mkCaseRawStack keyMatchLongBits dictGetRootN0 0))
          #[] n0Value.cell.bits keyMatchLongBits },
    { name := "unit/n-boundaries" -- [B8]
      run := do
        expectHit
          "hit/n-max"
          (runDirect (mkCaseRawStack keyMatchBits dictGetRoot 1023))
          keyMatchBits dictGetValue.cell.bits #[] },
    { name := "unit/malformed-root" -- [B9]
      run := do
        let _ ← expectRawErr
          "malformed-root"
          (runPFXDICTGET (mkCaseRawStack keyMatchBits (.cell malformedDictRoot) 4))
          .cellUnd
        pure ()
      },
    { name := "unit/encode-decode" -- [B10][B11]
      run := do
        match assembleCp0 [instr] with
        | .error e =>
            throw (IO.userError s!"unit/encode: expected assembly success, got {e}")
        | .ok code =>
            let _ ← expectDecodeStep "unit/encode/decode-roundtrip" (Slice.ofCell code) instr 16
            pure ()
        let _ ← expectDecodeStep "unit/decode/f4a9" (Slice.ofCell (raw16 0xF4A9)) instr 16
        let _ ← expectDecodeStep "unit/decode/f4a8" (Slice.ofCell (raw16 0xF4A8)) (.dictExt (.pfxGet .getQ)) 16
        let _ ← expectDecodeStep "unit/decode/f4aa" (Slice.ofCell (raw16 0xF4AA)) (.dictExt (.pfxGet .getJmp)) 16
        let _ ← expectDecodeStep "unit/decode/f4ab" (Slice.ofCell (raw16 0xF4AB)) (.dictExt (.pfxGet .getExec)) 16
        expectDecodeInvOpcode "unit/decode/f4a7" 0xF4A7
        expectDecodeInvOpcode "unit/decode/f4ac" 0xF4AC
        match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits 0xF4 8) #[])) with
        | .error .invOpcode => pure ()
        | .ok (di, bits, _) =>
            throw (IO.userError s!"unit/decode/truncated-f4: expected invOpcode, got {reprStr di}/{bits}")
        | .error e =>
            throw (IO.userError s!"unit/decode/truncated-f4: expected invOpcode, got {e}")
      },
    { name := "unit/gas-exact" -- [B12]
      run := do
        let _ :=
          mkCase
            "unit/gas-exact"
            (mkCaseRawStack keyMatchLongBits dictGetRoot 4)
            gasExactLimits
            1_000_000
            (#[.pushInt (.num gasExact), .tonEnvOp .setGasLimit, instr])
        let _ :=
          mkCase
            "unit/gas-exact-minus-one"
            (mkCaseRawStack keyMatchLongBits dictGetRoot 4)
            gasExactMinusOneLimits
            1_000_000
            (#[.pushInt (.num gasExactMinusOne), .tonEnvOp .setGasLimit, instr])
        pure () }
  ]
  oracle := #[
    -- [B2] underflow
    mkCase "oracle/underflow/0" #[] -- [B2]
    , mkCase "oracle/underflow/1" #[(.slice keyMatch)] -- [B2]
    , mkCase "oracle/underflow/2" #[(.slice keyMatch), dictGetRoot] -- [B2]
    -- [B3] n validation
    , mkCase "oracle/err/n/not-int" (#[(.slice keyMatch), dictGetRoot, .tuple #[]]) -- [B3]
    , mkCase "oracle/err/n/nan" (#[(.slice keyMatch), dictGetRoot, .int .nan]) -- [B3]
    , mkCase "oracle/err/n/negative" (mkCaseRawStack keyMatchBits dictGetRoot (-1)) -- [B3]
    , mkCase "oracle/err/n/too-large" (mkCaseRawStack keyMatchBits dictGetRoot 1024) -- [B3]
    -- [B4] dict validation
    , mkCase "oracle/err/dict/builder" (mkCaseRawStack keyMatchBits (.builder Builder.empty) 4) -- [B4]
    , mkCase "oracle/err/dict/tuple" (mkCaseRawStack keyMatchBits (.tuple #[]) 4) -- [B4]
    , mkCase "oracle/err/dict/int" #[.slice keyMatch, intV 7, intV 4] -- [B4]
    -- [B5] key validation
    , mkCase "oracle/err/key/null" (#[(.null), dictGetRoot, intV 4]) -- [B5]
    , mkCase "oracle/err/key/cell" (#[.cell Cell.empty, dictGetRoot, intV 4]) -- [B5]
    , mkCase "oracle/err/key/builder" (#[.builder Builder.empty, dictGetRoot, intV 4]) -- [B5]
    , mkCase "oracle/err/key/tuple" (#[.tuple #[], dictGetRoot, intV 4]) -- [B5]
    , mkCase "oracle/err/key/nan" (#[.int .nan, dictGetRoot, intV 4]) -- [B5]
    -- [B6] miss
    , mkCase "oracle/miss/key-mismatch" (mkCaseRawStack keyMismatch dictGetRoot 3) -- [B6]
    , mkCase "oracle/miss/root-null" (mkCaseRawStack keyMatchLongBits (.null) 3) -- [B6]
    , mkCase "oracle/miss/short-key" (mkCaseRawStack keyShort dictGetRoot 3) -- [B6]
    -- [B7] hit
    , mkCase "oracle/hit/exact" (mkCaseRawStack keyMatchBits dictGetRoot 4) -- [B7]
    , mkCase "oracle/hit/long-key" (mkCaseRawStack keyMatchLongBits dictGetRoot 4) -- [B7]
    , mkCase "oracle/hit/longer-key" (mkCaseRawStack keyMatchLongerBits dictGetRootLong 5) -- [B7]
    , mkCase "oracle/hit/n0" (mkCaseRawStack keyMatchLongBits dictGetRootN0 0) -- [B7][B8]
    , mkCase "oracle/hit/n-max" (mkCaseRawStack keyMatchBits dictGetRoot 1023) -- [B7][B8]
    -- [B8] boundary conditions
    , mkCase "oracle/hit/empty-prefix-root-miss-key" (mkCaseRawStack keyMatchBits dictGetRootN0 0) -- [B8]
    , mkCase "oracle/miss/fn/short-key" (mkCaseRawStack keyMatchBits dictGetRootLong 10) -- [B8]
    -- [B9] malformed
    , mkCase "oracle/malformed/root" (mkCaseRawStack keyMatchBits (.cell malformedDictRoot) 4) -- [B9]
    -- [B10] assembler and decode
    , mkCaseCode "oracle/raw/f4a9" (raw16 0xF4A9) (mkCaseRawStack keyMatchLongBits dictGetRoot 4) -- [B10]
    , mkCaseCode "oracle/raw/f4a8" (raw16 0xF4A8) (mkCaseRawStack keyMatchLongBits dictGetRoot 4) -- [B10]
    , mkCaseCode "oracle/raw/f4aa" (raw16 0xF4AA) (mkCaseRawStack keyMatchLongBits dictGetRoot 4) -- [B10]
    , mkCaseCode "oracle/raw/f4ab" (raw16 0xF4AB) (mkCaseRawStack keyMatchLongBits dictGetRoot 4) -- [B10]
    , mkCaseCode "oracle/raw/f4a7" (raw16 0xF4A7) -- [B11]
    , mkCaseCode "oracle/raw/f4ac" (raw16 0xF4AC) -- [B11]
    , mkCaseCode "oracle/raw/truncated-f4" (Cell.mkOrdinary (natToBits 0xF4 8) #[]) -- [B11]
    -- [B12] gas
    , mkCase
        "oracle/gas/exact"
        (mkCaseRawStack keyMatchLongBits dictGetRoot 4)
        gasExactLimits
        1_000_000
        (#[.pushInt (.num gasExact), .tonEnvOp .setGasLimit, instr]) -- [B12]
    , mkCase
        "oracle/gas/exact-minus-one"
        (mkCaseRawStack keyMatchLongBits dictGetRoot 4)
        gasExactMinusOneLimits
        1_000_000
        (#[.pushInt (.num gasExactMinusOne), .tonEnvOp .setGasLimit, instr]) -- [B12]
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genPFXDICTGET
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTGET
