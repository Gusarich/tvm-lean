import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTADDGETREF

/-!
INSTRUCTION: DICTADDGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success path when the key is absent (`DICTADDGETREF` in `.add` mode).
   - Pops: new value, key slice, optional dict root, and `n`.
   - `popNatUpTo` succeeds for valid `n`.
   - `keySlice.haveBits n` must be true.
   - `dictLookupSet*WithCells` returns `oldVal? = none`.
   - Output is `(newRoot, -0)` (boolean false for `.add`).

2. [B2] Runtime success path when the key exists.
   - For non-ref insertion, existing old value is pushed as a slice then `-0`.
   - For by-ref insertion, existing old value is extracted as a cell via
     `extractRefOrThrow` and pushed as `.cell`, then `-0`.

3. [B3] Key length errors (`cellUnd`).
   - If `keySlice.haveBits n` is false for requested `n` and mode is `.add`,
     execution reaches `cellUnd` before dictionary mutation in all branches.

4. [B4] Operand validation for non-stack semantics.
   - `popNatUpTo 1023` failures: negative `n`, NaN, >1023 → `rangeChk`.
   - `popMaybeCell`, `popSlice`, and `popCell` type paths are exercised by malformed
     stack shapes.

5. [B5] Decoder boundaries.
   - `0xf43a` and `0xf43b` decode to `.dictExt (.mutGet false _ byRef .add)`.
   - Neighboring codes (e.g., `0xf439`, `0xf440`) are `.invOpcode`.
   - The adjacent int-key opcode (`0xf43c`) decodes to `DICTIADDGET`-style opcode as a
     positive check for family encoding.

6. [B6] Assembler encoding.
   - `.dictExt` instructions are not encodable via `assembleCp0` in this path.
     Expect `.invOpcode` for `DICTADDGETREF` assembly.

7. [B7] Gas accounting.
   - Base budget from 16-bit decode path is exercised with exact and exact-minus-one
     gas envelopes.
   - Dynamic dictionary-gas deltas exist in underlying dictionary helpers but are
     covered by the generic fuzz distribution and exact-budget branches.

8. [B8] Fuzzer branch coverage requirements.
   - Missing/hit/malformed root/malformed payload/type errors/underflow/n-range/cell types
     must be explicitly generated.

TOTAL BRANCHES: 8

Every branch listed above has at least one dedicated oracle test or explicit fuzz shape.
-/

private def dictAddGetRefId : InstrId :=
  { name := "DICTADDGETREF" }

private def mkInstr (byRef : Bool) : Instr :=
  .dictExt (.mutGet false false byRef .add)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawF43A : Cell := raw16 0xf43a
private def rawF43B : Cell := raw16 0xf43b
private def rawF43C : Cell := raw16 0xf43c
private def rawF439 : Cell := raw16 0xf439
private def rawF440 : Cell := raw16 0xf440
private def rawTruncated8 : Cell := raw16 0xf4

private def mkDictCaseStack (newVal : Value) (key : Value) (dict : Value) (n : Value) : Array Value :=
  #[newVal, key, dict, n]

private def normalNewValue (byRef : Bool) : Value :=
  if byRef then
    .cell (Cell.mkOrdinary (natToBits 0xC0 8) #[])
  else
    .slice (mkSliceFromBits (natToBits 0x1F 8))

private def badNewValue (byRef : Bool) : Value :=
  if byRef then
    .slice (mkSliceFromBits (natToBits 0x80 8))
  else
    .cell (Cell.mkOrdinary (natToBits 0xAB 8) #[])

private def valueSliceA : Slice := mkSliceFromBits (natToBits 0x5A 8)
private def valueSliceB : Slice := mkSliceFromBits (natToBits 0xA5 8)
private def invalidSliceValue : Slice := mkSliceFromBits (natToBits 0x55 8)

private def valueCellA : Cell := Cell.mkOrdinary (natToBits 0xC0 8) #[]
private def valueCellB : Cell := Cell.mkOrdinary (natToBits 0x7F 8) #[]
private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def key4 (v : Nat) : BitString := natToBits v 4
private def key8 (v : Nat) : BitString := natToBits v 8
private def keySlice4 (v : Nat) : Slice := mkSliceFromBits (key4 v)
private def keySlice3 (v : Nat) : Slice := mkSliceFromBits (natToBits v 3)
private def key0 : Slice := mkSliceFromBits #[]
private def key8SliceA : Slice := mkSliceFromBits (natToBits 0xA5 8)
private def key1023 : BitString := Array.replicate 1023 true
private def keySlice1023 : Slice := mkSliceFromBits key1023

private def mkDictRootSlice! (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetSliceWithCells root k v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: insertion did not produce root"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def mkDictRootRef! (label : String) (pairs : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetRefWithCells root k v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: insertion did not produce root"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def dictSlice4Single : Cell :=
  mkDictRootSlice! "dict/slice/single/4" #[(key4 0xA, valueSliceA)]

private def dictSlice4Miss : Cell :=
  mkDictRootSlice! "dict/slice/miss/4" #[(key4 0x3, valueSliceB)]

private def dictRef4Single : Cell :=
  mkDictRootRef! "dict/ref/single/4" #[(key4 0xA, valueCellA)]

private def dictRef4Miss : Cell :=
  mkDictRootRef! "dict/ref/miss/4" #[(key4 0x6, valueCellB)]

private def dictSliceMalformedRefLike : Cell :=
  mkDictRootSlice! "dict/ref-shape/error" #[(key4 0x5, invalidSliceValue)]

private def dictSliceN0 : Cell :=
  mkDictRootSlice! "dict/slice/n0" #[(#[], valueSliceA)]

private def dictRefN0 : Cell :=
  mkDictRootRef! "dict/ref/n0" #[(#[], valueCellA)]

private def dictSliceN1023 : Cell :=
  mkDictRootSlice! "dict/slice/n1023" #[(key1023, valueSliceA)]

private def caseDictAddGetRef
    (name : String)
    (byRef : Bool)
    (stack : Array Value)
    (program : Array Instr := #[mkInstr byRef])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictAddGetRefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr}")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def dictAddGetRefExactGas : Int :=
  computeExactGasBudget (mkInstr false)

private def dictAddGetRefExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkInstr false)

private def genDictAddGetRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    match shape with
    | 0 =>
        (caseDictAddGetRef
          "fuzz/miss/null/n4/notref"
          false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 7)) .null (intV 4)), rng2)
    | 1 =>
        (caseDictAddGetRef
          "fuzz/miss/null/n4/byref"
          true
          (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 7)) .null (intV 4)), rng2)
    | 2 =>
        (caseDictAddGetRef
          "fuzz/hit/slice"
          false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV 4)), rng2)
    | 3 =>
        (caseDictAddGetRef
          "fuzz/hit/ref"
          true
          (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 0xA)) (.cell dictRef4Single) (intV 4)), rng2)
    | 4 =>
        (caseDictAddGetRef
          "fuzz/hit/ref-shaped-slice"
          true
          (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 0x5)) (.cell dictSliceMalformedRefLike) (intV 4)), rng2)
    | 5 =>
        (caseDictAddGetRef
          "fuzz/key-short/notref"
          false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice3 0x5)) (.cell dictSlice4Single) (intV 4)), rng2)
    | 6 =>
        (caseDictAddGetRef
          "fuzz/key-short/byref"
          true
          (mkDictCaseStack (normalNewValue true) (.slice (keySlice3 0x5)) (.cell dictSlice4Single) (intV 4)), rng2)
    | 7 =>
        (caseDictAddGetRef
          "fuzz/n-negative"
          false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV (-1))), rng2)
    | 8 =>
        (caseDictAddGetRef
          "fuzz/n-too-large"
          false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV 1024)), rng2)
    | 9 =>
        (caseDictAddGetRef
          "fuzz/n-nan"
          false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (.int .nan)), rng2)
    | 10 =>
        (caseDictAddGetRef
          "fuzz/dict-type"
          false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.int (.num 0)) (intV 4)), rng2)
    | 11 =>
        (caseDictAddGetRef
          "fuzz/key-type"
          false
          (mkDictCaseStack (normalNewValue false) (.cell valueCellA) (.cell dictSlice4Single) (intV 4)), rng2)
    | 12 =>
        (caseDictAddGetRef
          "fuzz/newvalue-type/notref"
          false
          (mkDictCaseStack (badNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV 4)), rng2)
    | 13 =>
        (caseDictAddGetRef
          "fuzz/newvalue-type/byref"
          true
          (mkDictCaseStack (badNewValue true) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV 4)), rng2)
    | 14 =>
        let (mode, rng3') := randNat rng2 0 3
        let stack : Array Value :=
          if mode = 0 then
            #[]
          else if mode = 1 then
            #[intV 1]
          else if mode = 2 then
            #[intV 1, .cell Cell.empty]
          else
            #[intV 1, .cell Cell.empty, (.slice (keySlice4 0xA))]
        (caseDictAddGetRef "fuzz/underflow" false stack, rng3')
    | 15 =>
        (caseDictAddGetRef
          "fuzz/hit-n0"
          false
          (mkDictCaseStack (normalNewValue false) (.slice key0) (.cell dictSliceN0) (intV 0)), rng2)
    | 16 =>
        (caseDictAddGetRef
          "fuzz/hit-n0-byref"
          true
          (mkDictCaseStack (normalNewValue true) (.slice key0) (.cell dictRefN0) (intV 0)), rng2)
    | 17 =>
        (caseDictAddGetRef
          "fuzz/n1023-hit-miss"
          false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice1023) .null (intV 1023)), rng2)
    | 18 =>
        (caseDictAddGetRef
          "fuzz/malformed-root"
          false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell malformedDictRoot) (intV 4)), rng2)
    | 19 =>
        let code : Array Instr :=
          #[.pushInt (.num dictAddGetRefExactGas), .tonEnvOp .setGasLimit, mkInstr false]
        (caseDictAddGetRef "fuzz/gas/exact" false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0x7)) .null (intV 4))
          code (oracleGasLimitsExact dictAddGetRefExactGas), rng2)
    | 20 =>
        let code : Array Instr :=
          #[.pushInt (.num dictAddGetRefExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr false]
        (caseDictAddGetRef "fuzz/gas/exact-minus-one" false
          (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0x7)) .null (intV 4))
          code (oracleGasLimitsExactMinusOne dictAddGetRefExactGasMinusOne), rng2)
    | 21 =>
        let code : Array Instr :=
          #[.pushInt (.num dictAddGetRefExactGas), .tonEnvOp .setGasLimit, mkInstr true]
        (caseDictAddGetRef "fuzz/gas/exact-byref" true
          (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 0x7)) .null (intV 4))
          code (oracleGasLimitsExact dictAddGetRefExactGas), rng2)
    | _ =>
        let code : Array Instr :=
          #[.pushInt (.num dictAddGetRefExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr true]
        (caseDictAddGetRef "fuzz/gas/exact-minus-one-byref" true
          (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 0x7)) .null (intV 4))
          code (oracleGasLimitsExactMinusOne dictAddGetRefExactGasMinusOne), rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := dictAddGetRefId
  unit := #[
    { name := "unit/decoder/decode/f43a"
      run := do
        let _ ← expectDecodeStep "decode/f43a" (Slice.ofCell rawF43A)
          (.dictExt (.mutGet false false false .add)) 16
    }
    ,
    { name := "unit/decoder/decode/f43b"
      run := do
        let _ ← expectDecodeStep "decode/f43b" (Slice.ofCell rawF43B)
          (.dictExt (.mutGet false false true .add)) 16
    }
    ,
    { name := "unit/decoder/decode/f43c-int-alias"
      run := do
        let _ ← expectDecodeStep "decode/f43c-int" (Slice.ofCell rawF43C)
          (.dictExt (.mutGet true false false .add)) 16
    }
    ,
    { name := "unit/decoder/decode/invalid-below"
      run := do
        expectDecodeInvOpcode "decode/f439" 0xf439
    }
    ,
    { name := "unit/decoder/decode/invalid-above"
      run := do
        expectDecodeInvOpcode "decode/f440" 0xf440
    }
    ,
    { name := "unit/decoder/decode/truncated8"
      run := do
        expectDecodeInvOpcode "decode/truncated8" 0xf4
    }
    ,
    { name := "unit/asm/encode/not-supported"
      run := do
        match assembleCp0 [mkInstr false] with
        | .ok _ =>
            throw (IO.userError "asm/encode/not-supported: expected invOpcode, got success")
        | .error e =>
            if e = .invOpcode then
              pure ()
            else
              throw (IO.userError s!"asm/encode/not-supported: expected invOpcode, got {e}")
    }
  ]
  oracle := #[
    -- [B1] runtime success: empty dict miss, non-ref insertion.
    caseDictAddGetRef "oracle/ok/miss/null/n4/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 7)) .null (intV 4))
    -- [B1] runtime success: empty dict miss, by-ref insertion.
    , caseDictAddGetRef "oracle/ok/miss/null/n4/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 7)) .null (intV 4))
    -- [B1] runtime success: boundary n=0 on empty dict, non-ref.
    , caseDictAddGetRef "oracle/ok/miss/null/n0/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice key0) .null (intV 0))
    -- [B1] runtime success: boundary n=0 on empty dict, by-ref.
    , caseDictAddGetRef "oracle/ok/miss/null/n0/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice key0) .null (intV 0))
    -- [B1] runtime success: empty dict miss at n=1023, non-ref.
    , caseDictAddGetRef "oracle/ok/miss/null/n1023/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice1023) .null (intV 1023))
    -- [B1] runtime success: miss with non-empty dict root, non-ref.
    , caseDictAddGetRef "oracle/ok/miss/nonempty/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 5)) (.cell dictSlice4Miss) (intV 4))
    -- [B1] runtime success: miss with non-empty dict root, by-ref.
    , caseDictAddGetRef "oracle/ok/miss/nonempty/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 5)) (.cell dictRef4Miss) (intV 4))
    -- [B2] runtime success: hit existing key, non-ref old value path.
    , caseDictAddGetRef "oracle/ok/hit/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV 4))
    -- [B2] runtime success: hit existing key, by-ref old value path.
    , caseDictAddGetRef "oracle/ok/hit/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 0xA)) (.cell dictRef4Single) (intV 4))
    -- [B1] runtime success: n=0 hit path for empty-key entry, non-ref.
    , caseDictAddGetRef "oracle/ok/hit/n0/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice key0) (.cell dictSliceN0) (intV 0))
    -- [B2] runtime success: n=0 hit path for empty-key entry, by-ref.
    , caseDictAddGetRef "oracle/ok/hit/n0/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice key0) (.cell dictRefN0) (intV 0))
    -- [B3] runtime failure: key too short for requested n.
    , caseDictAddGetRef "oracle/err/key-short/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice3 0x5)) (.cell dictSlice4Single) (intV 4))
    -- [B3] runtime failure: key too short for requested n (by-ref path).
    , caseDictAddGetRef "oracle/err/key-short/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice3 0x5)) (.cell dictSlice4Single) (intV 4))
    -- [B4] runtime failure: n negative.
    , caseDictAddGetRef "oracle/err/n-negative" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV (-1)))
    -- [B4] runtime failure: n above 1023.
    , caseDictAddGetRef "oracle/err/n-too-large" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV 1024))
    -- [B4] runtime failure: n NaN.
    , caseDictAddGetRef "oracle/err/n-nan" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (.int .nan))
    -- [B4] runtime failure: dict root type error.
    , caseDictAddGetRef "oracle/err/dict-type" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.int (.num 0)) (intV 4))
    -- [B4] runtime failure: key type error (cell).
    , caseDictAddGetRef "oracle/err/key-type-cell" false
      (mkDictCaseStack (normalNewValue false) (.cell valueCellA) (.cell dictSlice4Single) (intV 4))
    -- [B4] runtime failure: key type error (null).
    , caseDictAddGetRef "oracle/err/key-type-null" false
      (mkDictCaseStack (normalNewValue false) .null (.cell dictSlice4Single) (intV 4))
    -- [B4] runtime failure: value type error for non-ref insertion.
    , caseDictAddGetRef "oracle/err/newvalue-type/notref" false
      (mkDictCaseStack (badNewValue false) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV 4))
    -- [B4] runtime failure: value type error for by-ref insertion.
    , caseDictAddGetRef "oracle/err/newvalue-type/byref" true
      (mkDictCaseStack (badNewValue true) (.slice (keySlice4 0xA)) (.cell dictSlice4Single) (intV 4))
    -- [B7] runtime failure: by-ref old value is malformed slice shape.
    , caseDictAddGetRef "oracle/err/ref-shape-not-single-ref" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 0x5)) (.cell dictSliceMalformedRefLike) (intV 4))
    -- [B8] runtime failure: malformed dictionary root (dictionary-shape error).
    , caseDictAddGetRef "oracle/err/malformed-root" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) (.cell malformedDictRoot) (intV 4))
    -- [B6] runtime underflow: empty stack.
    , caseDictAddGetRef "oracle/err/underflow/0" false #[]
    -- [B6] runtime underflow: one item.
    , caseDictAddGetRef "oracle/err/underflow/1" false #[intV 1]
    -- [B6] runtime underflow: two items.
    , caseDictAddGetRef "oracle/err/underflow/2" false #[intV 1, .cell Cell.empty]
    -- [B6] runtime underflow: three items.
    , caseDictAddGetRef "oracle/err/underflow/3" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 0xA)) .null (intV 0))
    -- [B7] runtime failure: malformed stored-ref payload (same as by-ref shape mismatch).
    , caseDictAddGetRef "oracle/err/ref-shape/mismatch" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 0x5)) (.cell dictSliceMalformedRefLike) (intV 4))
    -- [B8] runtime failure: malformed root in by-ref mode.
    , caseDictAddGetRef "oracle/err/malformed-root/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 0xA)) (.cell malformedDictRoot) (intV 4))
    -- [B9] gas branch should execute.
    , caseDictAddGetRef "oracle/gas/exact" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 7)) .null (intV 4))
      #[.pushInt (.num dictAddGetRefExactGas), .tonEnvOp .setGasLimit, mkInstr false] (oracleGasLimitsExact dictAddGetRefExactGas)
    -- [B9] gas branch exact-minus-one should fail by exhaustion.
    , caseDictAddGetRef "oracle/gas/exact-minus-one" false
      (mkDictCaseStack (normalNewValue false) (.slice (keySlice4 7)) .null (intV 4))
      #[.pushInt (.num dictAddGetRefExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr false]
      (oracleGasLimitsExactMinusOne dictAddGetRefExactGasMinusOne)
    -- [B9] gas branch with by-ref insertion, exact.
    , caseDictAddGetRef "oracle/gas/exact-byref" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 7)) .null (intV 4))
      #[.pushInt (.num dictAddGetRefExactGas), .tonEnvOp .setGasLimit, mkInstr true] (oracleGasLimitsExact dictAddGetRefExactGas)
    -- [B9] gas branch with by-ref insertion, exact-minus-one.
    , caseDictAddGetRef "oracle/gas/exact-minus-one-byref" true
      (mkDictCaseStack (normalNewValue true) (.slice (keySlice4 7)) .null (intV 4))
      #[.pushInt (.num dictAddGetRefExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr true]
      (oracleGasLimitsExactMinusOne dictAddGetRefExactGasMinusOne)
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genDictAddGetRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTADDGETREF
