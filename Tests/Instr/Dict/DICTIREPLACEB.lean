import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREPLACEB

/-
INSTRUCTION: DICTIREPLACEB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Signed integer runtime success path:
   `n <- popNatUpTo 1023`, `dictCell <- popMaybeCell`, `key <- popInt`,
   `keyBits <- dictKeyBits?` (signed mode), `value <- popBuilder`, and
   `dictSetBuilderWithCells keyBits .replace` returns `(newRoot, true, created, loaded)`.
   The VM pushes `newRoot` and `-1`; `created` controls optional extra gas.
2. [B2] Unsigned-integer runtime success path:
   same as [B1], but with `unsigned = true`; keys are interpreted as unsigned
   0..2^n-1 when computing `keyBits`.
3. [B3] Successful replace miss path:
   Dictionary insertion not required for replace mode; if key is not present, `ok=false`
   and VM pushes `null` and `0` for all variants.
4. [B4] Slice-key runtime success path:
   for `.dictReplaceB false _`, `key <- popSlice`; `haveBits n` must hold
   (`cellUnd` otherwise), and `readBits n` is used as `keyBits`.
5. [B5] Underflow branch:
   `VM.checkUnderflow 4` is enforced before any pops.
6. [B6] Range/type failure branches:
   - `n` must satisfy `0 ≤ n ≤ 1023`; violations produce `.rangeChk`.
   - `key` must be integer in integer mode; `.nan` and out-of-range values produce
     `.rangeChk` for both signed and unsigned modes.
   - `dictCell` must be maybe-cell, `key` must be int/slice by mode,
     and top-of-stack value must be builder.
7. [B7] Slice mode validation failure:
   slice key with `slice.haveBits n = false` maps to `none` then `.cellUnd`.
8. [B8] Malformed dictionary branch:
   `dictSetBuilderWithCells` for bad existing roots may return `.dictErr`; execution
   reraises that error after registering loaded cells.
9. [B9] Assembler encoding branch:
   `.dictReplaceB false false` -> `0xf449`,
   `.dictReplaceB true false` -> `0xf44a`,
   `.dictReplaceB true true` -> `0xf44b`.
   `.dictReplaceB false true` is invalid and must raise `.invOpcode`.
10. [B10] Decoder branch:
    opcodes `0xf449..0xf44c` decode to the three valid forms above.
    Adjacent opcodes `0xf448` and `0xf44c` are invalid for this opcode family.
11. [B11] Gas exactness branch:
    base instruction gas (from `computeExactGasBudget`) should pass at exact and fail
    at exact-1.
12. [B12] Variable gas penalty branch:
    success with `created > 0` adds `created * cellCreateGasPrice`.
    In replace mode this occurs on existing-key hit paths.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests should be covered by the fuzz generator.
-/

private def dictReplaceBId : InstrId := { name := "DICTIREPLACEB" }

private def dictReplaceBSlice : Instr := .dictReplaceB false false
private def dictReplaceBSigned : Instr := .dictReplaceB true false
private def dictReplaceBSignedUnsigned : Instr := .dictReplaceB true true

private def rawF449 : Cell := Cell.mkOrdinary (natToBits 0xf449 16) #[]
private def rawF44A : Cell := Cell.mkOrdinary (natToBits 0xf44a 16) #[]
private def rawF44B : Cell := Cell.mkOrdinary (natToBits 0xf44b 16) #[]
private def rawF448 : Cell := Cell.mkOrdinary (natToBits 0xf448 16) #[]
private def rawF44C : Cell := Cell.mkOrdinary (natToBits 0xf44c 16) #[]

private def sampleValueA : Builder := Builder.empty.storeBits (natToBits 0xAA 8)
private def sampleValueB : Builder := Builder.empty.storeBits (natToBits 0xBB 8)
private def sampleValueC : Builder := Builder.empty.storeBits (natToBits 0xCC 8)
private def sampleValueD : Builder := Builder.empty.storeBits (natToBits 0xDD 8)
private def sampleValueE : Builder := Builder.empty.storeBits (natToBits 0x11 8)
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkDictInt! (label : String) (n : Nat) (unsigned : Bool)
    (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in pairs do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n unsigned with
        | some bs => bs
        | none => panic! s!"DICTIREPLACEB: {label}: out-of-range int key k={k}, n={n}, unsigned={unsigned}"
      match dictSetBuilderWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"DICTIREPLACEB: {label}: unexpected empty root after set"
      | .error e =>
          panic! s!"DICTIREPLACEB: {label}: dict build failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"DICTIREPLACEB: {label}: empty dict after construction"

private def mkDictBits! (label : String) (pairs : Array (BitString × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in pairs do
      let (k, v) := entry
      match dictSetBuilderWithCells root k v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"DICTIREPLACEB: {label}: unexpected empty root after set"
      | .error e =>
          panic! s!"DICTIREPLACEB: {label}: dict build failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"DICTIREPLACEB: {label}: empty dict after construction"

private def dictSigned0 : Cell :=
  mkDictInt! "dictSigned0" 0 false #[
    (0, sampleValueA)
  ]

private def dictSigned1 : Cell :=
  mkDictInt! "dictSigned1" 1 false #[
    (0, sampleValueB),
    (-1, sampleValueC)
  ]

private def dictSigned4 : Cell :=
  mkDictInt! "dictSigned4" 4 false #[
    (-8, sampleValueA),
    (-1, sampleValueB),
    (0, sampleValueC),
    (7, sampleValueD)
  ]

private def dictSigned8 : Cell :=
  mkDictInt! "dictSigned8" 8 false #[
    (-128, sampleValueA),
    (-1, sampleValueB),
    (0, sampleValueC),
    (42, sampleValueD),
    (127, sampleValueE)
  ]

private def dictUnsigned8 : Cell :=
  mkDictInt! "dictUnsigned8" 8 true #[
    (0, sampleValueA),
    (1, sampleValueB),
    (64, sampleValueC),
    (255, sampleValueD)
  ]

private def dictSlice8 : Cell :=
  mkDictBits! "dictSlice8" #[
    (natToBits 0 8, sampleValueA),
    (natToBits 42 8, sampleValueB),
    (natToBits 255 8, sampleValueC)
  ]

private def dictSlice4 : Cell :=
  mkDictBits! "dictSlice4" #[
    (natToBits 1 4, sampleValueA),
    (natToBits 6 4, sampleValueB)
  ]

private def slice8ExactA : Slice := mkSliceFromBits (natToBits 0 8)
private def slice8ExactB : Slice := mkSliceFromBits (natToBits 42 8)
private def slice8ExactC : Slice := mkSliceFromBits (natToBits 127 8)
private def slice8Miss : Slice := mkSliceFromBits (natToBits 170 8)
private def slice4ExactA : Slice := mkSliceFromBits (natToBits 1 4)
private def slice4Miss : Slice := mkSliceFromBits (natToBits 3 4)
private def sliceTooShortFor8 : Slice := mkSliceFromBits (natToBits 5 3)
private def sliceTooShortFor4 : Slice := mkSliceFromBits (natToBits 1 1)

private def mkIntStack
    (n : Int)
    (key : Int)
    (dict : Value := .null)
    (value : Builder := sampleValueA) : Array Value :=
  #[.builder value, intV key, dict, intV n]

private def mkSliceStack
    (n : Int)
    (key : Slice)
    (dict : Value := .null)
    (value : Builder := sampleValueA) : Array Value :=
  #[.builder value, .slice key, dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictReplaceBSigned])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictReplaceBId
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
    instr := dictReplaceBId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (instr : Instr)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack
    (#[] ++ #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr])
    gasLimits
    fuel

private def expectAssembleErr
    (label : String)
    (expected : Excno)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure {expected}, got success")

private def expectDecodeInv (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr} with {bits} bits")

private def replaceCreated (root : Cell) (n : Nat) (key : Int) (unsigned : Bool) : Nat :=
  match dictKeyBits? key n unsigned with
  | none => 0
  | some keyBits =>
      match dictSetBuilderWithCells (some root) keyBits sampleValueA .replace with
      | .ok (_, _, created, _) => created
      | .error _ => 0

private def replaceBaseGasSigned : Int := computeExactGasBudget dictReplaceBSigned
private def replaceBaseGasUnsigned : Int := computeExactGasBudget dictReplaceBSignedUnsigned

private def replaceGasMiss : Int := replaceBaseGasSigned
private def replaceGasMissMinusOne : Int := computeExactGasBudgetMinusOne dictReplaceBSigned

private def replaceSignedHitCreated : Nat := replaceCreated dictSigned8 8 42 false
private def replaceSignedHitGas : Int :=
  replaceBaseGasSigned + Int.ofNat replaceSignedHitCreated * cellCreateGasPrice
private def replaceSignedHitGasMinusOne : Int :=
  if replaceSignedHitGas > 0 then replaceSignedHitGas - 1 else 0

private def replaceUnsignedHitCreated : Nat := replaceCreated dictUnsigned8 8 255 true
private def replaceUnsignedHitGas : Int :=
  replaceBaseGasUnsigned + Int.ofNat replaceUnsignedHitCreated * cellCreateGasPrice
private def replaceUnsignedHitGasMinusOne : Int :=
  if replaceUnsignedHitGas > 0 then replaceUnsignedHitGas - 1 else 0

private def genDICTIREPLACEBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 16 then
    -- [B5] underflow branches
    let (idx, rng2) := randNat rng1 0 3
    let c : OracleCase :=
      if idx = 0 then
        mkCase "fuzz/underflow/empty" #[]
      else if idx = 1 then
        mkCase "fuzz/underflow/one" #[.builder sampleValueA]
      else if idx = 2 then
        mkCase "fuzz/underflow/two" #[.builder sampleValueA, intV 7]
      else
        mkCase "fuzz/underflow/three" #[.builder sampleValueA, intV 1, .null]
    (c, rng2)
  else if shape < 32 then
    -- [B1,B5] signed hits
    let (kSel, rng2) := randNat rng1 0 4
    let (n, dictV, key) : (Int × Value × Int) :=
      if kSel < 2 then
        (0, .cell dictSigned0, 0)
      else if kSel < 4 then
        (4, .cell dictSigned4, -8)
      else
        (8, .cell dictSigned8, 42)
    let stack := mkIntStack n key dictV
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase (s!"fuzz/signed-hit/{n}/{key}/{tag}") stack, rng3)
  else if shape < 40 then
    -- [B3,B5] signed miss
    let (kSel, rng2) := randNat rng1 0 4
    let (n, dictV, key) : (Int × Value × Int) :=
      if kSel < 2 then
        (4, .cell dictSigned4, 6)
      else if kSel < 4 then
        (8, .cell dictSigned8, 13)
      else
        (1, .null, 1)
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase (s!"fuzz/signed-miss/{n}/{key}/{tag}") (mkIntStack n key dictV), rng3)
  else if shape < 52 then
    -- [B2,B6] unsigned hits/misses
    let (kSel, rng2) := randBool rng1
    if kSel then
      (mkCase "fuzz/unsigned-hit" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueB), rng1)
    else
      (mkCase "fuzz/unsigned-miss" (mkIntStack 8 254 (.cell dictUnsigned8) sampleValueB), rng1)
  else if shape < 64 then
    -- [B4,B6,B7] slice success/miss/cellUnd
    let (sel, rng2) := randNat rng1 0 2
    if sel = 0 then
      (mkCase "fuzz/slice-hit" (mkSliceStack 8 slice8ExactB (.cell dictSlice8) sampleValueC) dictReplaceBSlice, rng2)
    else if sel = 1 then
      (mkCase "fuzz/slice-miss" (mkSliceStack 8 slice8Miss (.cell dictSlice8) sampleValueC) dictReplaceBSlice, rng2)
    else
      (mkCase "fuzz/slice-cellund" (mkSliceStack 8 sliceTooShortFor8 (.cell dictSlice8) sampleValueC) dictReplaceBSlice, rng2)
  else if shape < 76 then
    -- [B6,B8] range/type stress
    let (sel, rng2) := randNat rng1 0 3
    let (c, rng3) :=
      if sel = 0 then
        (mkCase "fuzz/range/n-negative" (mkIntStack (-1 : Int) 0 .null), rng2)
      else if sel = 1 then
        (mkCase "fuzz/range/n-too-large" (mkIntStack 1024 0 .null), rng2)
      else if sel = 2 then
        (mkCase "fuzz/range/int-key-out" (mkIntStack 4 64 .null), rng2)
      else
        (mkCase "fuzz/range/unsigned-key-out" (mkIntStack 8 (-1) (.cell dictUnsigned8) sampleValueA), rng2)
    (c, rng3)
  else if shape < 88 then
    -- [B8,B9] malformed dictionaries and type errors
    let (sel, rng2) := randNat rng1 0 4
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/type/value-not-builder" (#[] ++ [ .int (.num 7), intV 1, .cell dictSigned4, intV 4])
      else if sel = 1 then
        mkCase "fuzz/type/key-not-int" (#[] ++ [ .builder sampleValueA, .slice slice8ExactA, .cell dictSigned8, intV 8])
      else if sel = 2 then
        mkCase "fuzz/type/dict-not-maybe-cell" (mkIntStack 4 1 (.int (.num 5)))
      else if sel = 3 then
        mkCase "fuzz/dict/malformed-int" (mkIntStack 8 1 (.cell malformedDict) sampleValueA)
      else
        mkCase "fuzz/dict/malformed-slice" (mkSliceStack 8 slice8ExactA (.cell malformedDict) sampleValueA) dictReplaceBSlice
    (c, rng2)
  else
    -- [B11,B12] gas boundary probes
    let (sel, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkGasCase "fuzz/gas/signed-miss-exact"
          (mkIntStack 0 1 .null) dictReplaceBSigned replaceGasMiss (oracleGasLimitsExact replaceGasMiss)
      else if sel = 1 then
        mkGasCase "fuzz/gas/signed-miss-exact-minus-one"
          (mkIntStack 0 1 .null) dictReplaceBSigned replaceGasMissMinusOne (oracleGasLimitsExactMinusOne replaceGasMiss)
      else if sel = 2 then
        mkGasCase "fuzz/gas/signed-hit-exact"
          (mkIntStack 8 42 (.cell dictSigned8) sampleValueA)
          dictReplaceBSigned replaceSignedHitGas (oracleGasLimitsExact replaceSignedHitGas)
      else if sel = 3 then
        mkGasCase "fuzz/gas/signed-hit-minus-one"
          (mkIntStack 8 42 (.cell dictSigned8) sampleValueA)
          dictReplaceBSigned replaceSignedHitGasMinusOne (oracleGasLimitsExactMinusOne replaceSignedHitGas)
      else if sel = 4 then
        mkGasCase "fuzz/gas/unsigned-hit-exact"
          (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueD)
          dictReplaceBSignedUnsigned replaceUnsignedHitGas (oracleGasLimitsExact replaceUnsignedHitGas)
      else
        mkGasCase "fuzz/gas/unsigned-hit-minus-one"
          (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueD)
          dictReplaceBSignedUnsigned replaceUnsignedHitGasMinusOne (oracleGasLimitsExactMinusOne replaceUnsignedHitGas)
    (c, rng2)

private def fuzzSeed : UInt64 := fuzzSeedForInstr dictReplaceBId

-- there are 30+ oracle cases below and each is tagged [B*].
def suite : InstrSuite where
  id := dictReplaceBId
  unit := #[
    { name := "unit/asm/valid-opcodes"
      run := do
        match assembleCp0 [dictReplaceBSlice] with
        | .ok _ => pure ()
        | .error e =>
            throw (IO.userError s!"unit/asm/valid/slice: expected success, got {e}")
        match assembleCp0 [dictReplaceBSigned] with
        | .ok _ => pure ()
        | .error e =>
            throw (IO.userError s!"unit/asm/valid/signed: expected success, got {e}")
        match assembleCp0 [dictReplaceBSignedUnsigned] with
        | .ok _ => pure ()
        | .error e =>
            throw (IO.userError s!"unit/asm/valid/unsigned: expected success, got {e}")
    },
    { name := "unit/asm/invalid-unsigned-slice"
      run := do
        expectAssembleErr "slice-unsigned-flag" .invOpcode (.dictReplaceB false true)
    },
    { name := "unit/decode/branches-and-boundaries" -- [B10]
      run := do
        let _ ← expectDecodeStep "decode/slice" (Slice.ofCell rawF449) (.dictReplaceB false false) 16
        let _ ← expectDecodeStep "decode/signed" (Slice.ofCell rawF44A) (.dictReplaceB true false) 16
        let _ ← expectDecodeStep "decode/unsigned" (Slice.ofCell rawF44B) (.dictReplaceB true true) 16
    },
    { name := "unit/decode/invalid-adjacent-opcodes" -- [B10]
      run := do
        expectDecodeInv "decode/0xf448-invalid" rawF448
        expectDecodeInv "decode/0xf44c-invalid" rawF44C
    }
  ]
  oracle := #[
    -- [B1] signed hit replaces existing key.
    mkCase "ok/signed-hit/n0/zero" (mkIntStack 0 0 (.cell dictSigned0) sampleValueB),
    -- [B1] signed hit replaces negative/edge key.
    mkCase "ok/signed-hit/n4/min" (mkIntStack 4 (-8) (.cell dictSigned4) sampleValueC),
    -- [B1] signed hit replaces positive key.
    mkCase "ok/signed-hit/n4/max" (mkIntStack 4 7 (.cell dictSigned4) sampleValueA),
    -- [B1] signed hit in larger width.
    mkCase "ok/signed-hit/n8/pos" (mkIntStack 8 42 (.cell dictSigned8) sampleValueD),
    -- [B2] signed miss on null.
    mkCase "ok/signed-miss/null" (mkIntStack 8 13 .null sampleValueA),
    -- [B2] signed miss with non-empty dict and absent key.
    mkCase "ok/signed-miss/nonempty" (mkIntStack 4 6 (.cell dictSigned4) sampleValueB),

    -- [B2] slice hit path.
    mkCase "ok/slice-hit/n8" (mkSliceStack 8 slice8ExactA (.cell dictSlice8) sampleValueA) dictReplaceBSlice,
    -- [B2] slice miss path.
    mkCase "ok/slice-miss/n8" (mkSliceStack 8 slice8Miss (.cell dictSlice8) sampleValueB) dictReplaceBSlice,
    -- [B4] n=0 allows only zero key.
    mkCase "ok/signed-hit/n0-nonneg" (mkIntStack 0 0 (.cell dictSigned0) sampleValueA),

    -- [B5] range errors: too large n.
    mkCase "err/range/n-too-large" (mkIntStack 1024 0 (.cell dictSigned8) sampleValueA),
    -- [B5] range errors: negative n.
    mkCase "err/range/n-negative" (mkIntStack (-1) 0 (.cell dictSigned8) sampleValueA),
    -- [B6] rangeChk on n=0 + non-zero key.
    mkCase "err/range/n0-nonzero" (mkIntStack 0 1 (.cell dictSigned0) sampleValueA),
    -- [B6] signed key out of range for n=4.
    mkCase "err/range/signed-key-high" (mkIntStack 4 8 (.cell dictSigned4) sampleValueA),
    -- [B6] signed key out of range low for n=4.
    mkCase "err/range/signed-key-low" (mkIntStack 4 (-9) (.cell dictSigned4) sampleValueA),
    -- [B6] unsigned mode rejects negative key.
    mkCase "err/range/unsigned-key-negative" (mkIntStack 8 (-1) (.cell dictUnsigned8) sampleValueD) dictReplaceBSignedUnsigned,
    -- [B6] unsigned mode rejects over-large key.
    mkCase "err/range/unsigned-key-high" (mkIntStack 8 256 (.cell dictUnsigned8) sampleValueD) dictReplaceBSignedUnsigned,

    -- [B7] slice key insufficient bits.
    mkCase "err/cellund/slice-missing-bits-8" (mkSliceStack 8 sliceTooShortFor8 (.cell dictSlice8) sampleValueC) dictReplaceBSlice,
    -- [B7] slice key insufficient bits for n=4.
    mkCase "err/cellund/slice-missing-bits-4" (mkSliceStack 4 sliceTooShortFor4 (.cell dictSlice4) sampleValueA) dictReplaceBSlice,

    -- [B8] underflow on stack depth.
    mkCase "err/underflow/empty" #[],
    mkCase "err/underflow/one" (#[] ++ [ .builder sampleValueA ]),
    mkCase "err/underflow/two" (#[] ++ [ .builder sampleValueA, intV 1 ]),
    mkCase "err/underflow/three" (#[] ++ [ .builder sampleValueA, intV 1, .cell dictSigned8 ]),

    -- [B8] type errors by argument order.
    mkCase "err/type/dict-not-maybe-cell" (mkIntStack 4 0 (.int (.num 7)) sampleValueA),
    mkCase "err/type/key-not-int" (#[] ++ [ .builder sampleValueA, .slice slice8ExactA, .cell dictSigned8, intV 8 ]),
    mkCase "err/type/key-nan" (#[] ++ [ .builder sampleValueA, .int .nan, .cell dictSigned8, intV 8 ]),
    mkCase "err/type/value-not-builder" (#[] ++ [ .int (.num 7), intV 3, .cell dictSigned4, intV 4 ]),
    mkCase "err/type/slice-value-on-int" (mkSliceStack 8 slice8ExactA (.cell dictSigned8) sampleValueA) dictReplaceBSigned, -- [B8] wrong top for int-key

    -- [B9] malformed dictionary branch.
    mkCase "err/dict-struct-invalid-int" (mkIntStack 8 1 (.cell malformedDict) sampleValueA),
    mkCase "err/dict-struct-invalid-slice" (mkSliceStack 8 slice8ExactA (.cell malformedDict) sampleValueA) dictReplaceBSlice,

    -- [B10] unsigned variant in normal and miss flow.
    mkCase "ok/unsigned-hit" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueD) dictReplaceBSignedUnsigned,
    mkCase "ok/unsigned-miss" (mkIntStack 8 2 (.cell dictUnsigned8) sampleValueD) dictReplaceBSignedUnsigned,

    -- [B11] exact-gas branches.
    mkGasCase "gas/signed-miss/exact" (mkIntStack 0 1 .null) dictReplaceBSigned replaceGasMiss (oracleGasLimitsExact replaceGasMiss),
    mkGasCase "gas/signed-miss/exact-minus-one" (mkIntStack 0 1 .null) dictReplaceBSigned replaceGasMissMinusOne (oracleGasLimitsExactMinusOne replaceGasMiss),
    mkGasCase "gas/signed-hit/exact" (mkIntStack 8 42 (.cell dictSigned8) sampleValueA) dictReplaceBSigned replaceSignedHitGas (oracleGasLimitsExact replaceSignedHitGas),
    mkGasCase "gas/signed-hit/exact-minus-one" (mkIntStack 8 42 (.cell dictSigned8) sampleValueA) dictReplaceBSigned replaceSignedHitGasMinusOne (oracleGasLimitsExactMinusOne replaceSignedHitGas),
    mkGasCase "gas/unsigned-hit/exact" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueD) dictReplaceBSignedUnsigned replaceUnsignedHitGas (oracleGasLimitsExact replaceUnsignedHitGas),
    mkGasCase "gas/unsigned-hit/exact-minus-one" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueD) dictReplaceBSignedUnsigned replaceUnsignedHitGasMinusOne (oracleGasLimitsExactMinusOne replaceUnsignedHitGas),

    -- [B10] decode-adjacent opcode runtime cases via explicit raw cells.
    mkCodeCase "ok/code-0xf449" (mkSliceStack 8 slice8ExactA (.cell dictSlice8) sampleValueA) (rawF449),
    mkCodeCase "ok/code-0xf44a" (mkIntStack 8 42 (.cell dictSigned8) sampleValueA) (rawF44A),
    mkCodeCase "ok/code-0xf44b" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueA) (rawF44B)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTIREPLACEBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREPLACEB
