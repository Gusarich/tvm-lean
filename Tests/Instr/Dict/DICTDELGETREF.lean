import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTDELGETREF

/-!
INSTRUCTION: DICTDELGETREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch dispatch branch:
   - `.dictExt (.mutGet false false true .del)` is handled only by
     `execInstrDictExt`; all other opcodes delegate to `next`.

2. [B2] Runtime underflow:
   - `VM.checkUnderflow 3` must fail for stacks with fewer than 3 items.

3. [B3] `n` validation path:
   - `VM.popNatUpTo 1023` accepts `n=1023`.
   - `n < 0`, `NaN`, and `n > 1023` all throw `.rangeChk`.

4. [B4] Runtime typing path:
   - `popMaybeCell` accepts `null` or `cell`; non-cell errors with `.typeChk`.
   - `popSlice` for key also requires top-of-stack to be a slice.

5. [B5] Runtime key-length path:
   - For slice keys, `keySlice.haveBits n` is required. Too few bits throws
     `.cellUnd`.

6. [B6] Runtime normal miss branch:
   - For key missing in `null`, `Cell.empty`, or non-empty dictionary roots,
     result is `(sameRoot, 0)`.

7. [B7] Runtime hit branch with valid stored reference value:
   - On hit and by-ref variant, `oldVal` is extracted as a cell if and only if
     returned slice has `bitsRemaining = 0` and `refsRemaining = 1`.
   - Result is `(newRoot, oldCell, -1)`.

8. [B8] Runtime malformed payload / non-reference branch:
   - Found key with leaf payload that is not exactly one ref and no bits
     (`extractRefOrThrow` predicate fails) throws `.dictErr`.

9. [B9] Runtime malformed dictionary shape:
   - Malformed dictionary root produces an error (e.g. `.cellUnd`/`.dictErr`) during
     deletion lookup.

10. [B10] Assembler encoding:
    - `Asm/Cp0` does not provide `dictExt` encoding; assembling
      `.dictExt (.mutGet false false true .del)` must return `.invOpcode`.

11. [B11] Decoder boundaries:
    - `0xf462..0xf463` decodes to non-int-key DELGET variants.
    - `0xf463` is the exact DICTDELGETREF decode target.
    - Gaps in the opcode map, such as `0xf468`, are expected to decode as `.invOpcode`.
    - Truncated input also fails decoding.

12. [B12] Gas accounting:
    - Base cost is fixed for 16-bit decode: `instrGas (.dictExt ... ) 16 = 26`.
    - Exact-gas success and exact-minus-one out-of-gas branches are tested.
    - If the payload/reference branch is taken, dynamic effects (`dictDeleteWithCells`
      created cells / loads) can add extra charges; tests here explicitly cover a base
      branch with `null` dictionary to make the gas boundary deterministic.

TOTAL BRANCHES: 12

Every oracle test below is tagged with the branch(es) it covers. Runtime, assembler,
decoder, and gas categories are explicitly represented; branches without direct
direct oracle cases are covered by fuzz.
-/

private def dictDelGetRefId : InstrId :=
  { name := "DICTDELGETREF" }

private def dictDelGetRefInstr : Instr :=
  .dictExt (.mutGet false false true .del)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawOpcode : Cell := raw16 0xf463

private def rawOpcodeLower : Cell := raw16 0xf462

private def rawOpcodeUpperNeighbor : Cell := raw16 0xf464

private def rawOpcodeGap : Cell := raw16 0xf468

private def rawTrunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def valueCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[]

private def valueCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x3C 8) #[]

private def valueCellC : Cell :=
  Cell.mkOrdinary (natToBits 0x77 8) #[]

private def valueSliceBad : Slice :=
  mkSliceFromBits (natToBits 0xFF 8)

private def valueCellRefBitsBad : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[valueCellA]

private def valueCellBitsOnly : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def valueCellNoRef : Cell :=
  Cell.mkOrdinary #[] #[]

private def valueCellTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[valueCellA, valueCellB]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def keyBits4 (v : Nat) : BitString :=
  natToBits v 4

private def keyBits8 (v : Nat) : BitString :=
  natToBits v 8

private def key4 (v : Nat) : Slice :=
  mkSliceFromBits (keyBits4 v)

private def key8 (v : Nat) : Slice :=
  mkSliceFromBits (keyBits8 v)

private def key1 : Slice :=
  mkSliceFromBits (natToBits 1 1)

private def key0 : Slice :=
  mkSliceFromBits #[]

private def key1023 : Slice :=
  mkSliceFromBits (Array.replicate 1023 true)

private def mkDictRefRoot! (label : String) (pairs : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetRefWithCells root k v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dict insertion produced no root for key {k}"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed with {e}"
    match root with
    | some d => d
    | none => panic! s!"{label}: empty dictionary after construction"

private def mkDictSliceRoot! (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetSliceWithCells root k v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dict insertion produced no root for key {k}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed with {e}"
    match root with
    | some d => d
    | none => panic! s!"{label}: empty dictionary after construction"

private def dict4SingleRef : Cell :=
  mkDictRefRoot! "dict4/single-ref" #[(keyBits4 0xA, valueCellA)]

private def dict4TwoRef : Cell :=
  mkDictRefRoot! "dict4/two-ref" #[(keyBits4 0xA, valueCellA), (keyBits4 0xB, valueCellB)]

private def dict4ThreeRef : Cell :=
  mkDictRefRoot! "dict4/three-ref" #[(keyBits4 0x2, valueCellC), (keyBits4 0xA, valueCellA), (keyBits4 0xB, valueCellB)]

private def dict4SingleSlice : Cell :=
  mkDictSliceRoot! "dict4/single-slice" #[(keyBits4 0xA, valueSliceBad)]

private def dict4SingleRefBitsBad : Cell :=
  mkDictRefRoot! "dict4/single-ref/bits" #[(keyBits4 0xA, valueCellRefBitsBad)]

private def dict4SingleRefBitsOnly : Cell :=
  mkDictRefRoot! "dict4/single-ref/bits-only" #[(keyBits4 0xA, valueCellBitsOnly)]

private def dict4SingleRefNoRef : Cell :=
  mkDictRefRoot! "dict4/single-ref/no-ref" #[(keyBits4 0xA, valueCellNoRef)]

private def dict4SingleRefTwoRefs : Cell :=
  mkDictRefRoot! "dict4/single-ref/two-refs" #[(keyBits4 0xA, valueCellTwoRefs)]

private def dict0Ref : Cell :=
  mkDictRefRoot! "dict0/ref" #[(#[], valueCellA)]

private def dict8SingleRef : Cell :=
  mkDictRefRoot! "dict8/single-ref" #[(keyBits8 0xA5, valueCellA)]

private def stack3 (k : Value) (d : Value) (n : Int) : Array Value :=
  #[k, d, intV n]

private def mkGasProgram (gasLimit : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gasLimit), .tonEnvOp .setGasLimit ] with
  | .ok c =>
      Cell.mkOrdinary (c.bits ++ natToBits 0xf463 16) #[]
  | .error e =>
      panic! s!"DICTDELGETREF gas-program prefix assembly failed: {reprStr e}"

private def dictDelGetRefBaseGas : Int :=
  instrGas dictDelGetRefInstr 16

private def dictDelGetRefBaseGasMinusOne : Int :=
  if dictDelGetRefBaseGas > 0 then
    dictDelGetRefBaseGas - 1
  else
    0

private def dictDelGetRefGasExact : OracleGasLimits :=
  { gasLimit := dictDelGetRefBaseGas
    gasMax := dictDelGetRefBaseGas
    gasCredit := 0 }

private def dictDelGetRefGasExactMinusOne : OracleGasLimits :=
  { gasLimit := dictDelGetRefBaseGasMinusOne
    gasMax := dictDelGetRefBaseGasMinusOne
    gasCredit := 0 }

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := rawOpcode)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelGetRefId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, rest) =>
      if instr != expected || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: unexpected decode result {reprStr instr}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeStepOrErr (label : String) (w16 : Nat) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (raw16 w16)) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {instr}/{bits}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def dispatchSentinel : Int := 909

private def runDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV dispatchSentinel)) stack

private def genDICTDELGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    if shape = 0 then
      (mkCase s!"fuzz/hit/single/{tag}" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRef) 4), rng2)
    else if shape = 1 then
      (mkCase s!"fuzz/hit/double-a/{tag}" (stack3 (.slice (key4 0xA)) (.cell dict4TwoRef) 4), rng2)
    else if shape = 2 then
      (mkCase s!"fuzz/hit/double-b/{tag}" (stack3 (.slice (key4 0xB)) (.cell dict4TwoRef) 4), rng2)
    else if shape = 3 then
      (mkCase s!"fuzz/hit/three/{tag}" (stack3 (.slice (key4 0x2)) (.cell dict4ThreeRef) 4), rng2)
    else if shape = 4 then
      (mkCase s!"fuzz/hit/n0/{tag}" (stack3 (.slice key0) (.cell dict0Ref) 0), rng2)
    else if shape = 5 then
      (mkCase s!"fuzz/hit/n8/{tag}" (stack3 (.slice (key8 0xA5)) (.cell dict8SingleRef) 8), rng2)
    else if shape = 6 then
      (mkCase s!"fuzz/hit/big-n/{tag}" (stack3 (.slice key1023) .null 1023), rng2)
    else if shape = 7 then
      (mkCase s!"fuzz/miss/null-4/{tag}" (stack3 (.slice (key4 0x1)) .null 4), rng2)
    else if shape = 8 then
      (mkCase s!"fuzz/miss/non-empty/{tag}" (stack3 (.slice (key4 0x1)) (.cell dict4SingleRef) 4), rng2)
    else if shape = 9 then
      (mkCase s!"fuzz/miss/non-empty-2/{tag}" (stack3 (.slice (key4 0x1)) (.cell dict4TwoRef) 4), rng2)
    else if shape = 10 then
      (mkCase s!"fuzz/miss/empty-key/{tag}" (stack3 (.slice key0) .null 4), rng2)
    else if shape = 11 then
      (mkCase s!"fuzz/miss/n1023/{tag}" (stack3 (.slice key1023) (.cell dict8SingleRef) 1023), rng2)
    else if shape = 12 then
      let (shape2, rng2') := randNat rng2 0 2
      let stack :=
        if shape2 = 0 then #[]
        else if shape2 = 1 then #[intV 1]
        else #[intV 1, intV 2]
      (mkCase s!"fuzz/err/underflow/{tag}" stack, rng2')
    else if shape = 13 then
      let (badN, rng2') := randNat rng2 0 1
      let n : Int := if badN = 0 then 1024 else -1
      (mkCase s!"fuzz/err/n-range/{tag}" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRef) n), rng2')
    else if shape = 14 then
    (mkCase s!"fuzz/err/n-nan/{tag}" #[.slice (key4 0xA), .cell dict4SingleRef, .int .nan], rng2)
    else if shape = 15 then
      (mkCase s!"fuzz/err/dict-type-int/{tag}" (stack3 (.slice (key4 0xA)) (.int (.num 0)) 4), rng2)
    else if shape = 16 then
      (mkCase s!"fuzz/err/key-type/{tag}" (stack3 (.cell valueCellA) (.cell dict4SingleRef) 4), rng2)
    else if shape = 17 then
      (mkCase s!"fuzz/err/key-short/{tag}" (stack3 (.slice key1) (.cell dict4SingleRef) 4), rng2)
    else if shape = 18 then
      (mkCase s!"fuzz/err/notref-slice/{tag}" (stack3 (.slice (key4 0xA)) (.cell dict4SingleSlice) 4), rng2)
    else if shape = 19 then
      (mkCase s!"fuzz/err/malformed-dict/{tag}" (stack3 (.slice (key4 0xA)) (.cell malformedDict) 4), rng2)
    else if shape = 20 then
      (mkCase s!"fuzz/err/notref-bits/{tag}" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRefBitsBad) 4), rng2)
    else if shape = 21 then
      (mkCase s!"fuzz/err/notref-bits-only/{tag}" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRefBitsOnly) 4), rng2)
    else if shape = 22 then
      (mkCase s!"fuzz/err/notref-no-ref/{tag}" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRefNoRef) 4), rng2)
    else if shape = 23 then
      (mkCase s!"fuzz/err/notref-two-refs/{tag}" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRefTwoRefs) 4), rng2)
    else if shape = 24 then
      (mkCase s!"fuzz/gas/exact/{tag}" (stack3 (.slice key0) .null 0) (mkGasProgram dictDelGetRefBaseGas) dictDelGetRefGasExact, rng2)
    else
      (mkCase s!"fuzz/gas/exact-minus-one/{tag}" (stack3 (.slice key0) .null 0)
          (mkGasProgram dictDelGetRefBaseGasMinusOne) dictDelGetRefGasExactMinusOne, rng2)

  ({ case0 with name := case0.name }, rng3)


def suite : InstrSuite where
  id := dictDelGetRefId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        let out := runDispatchFallback .add #[]
        expectOkStack "unit/dispatch/fallback" out #[intV dispatchSentinel] },
    { name := "unit/decode/self-ops"
      run := do
        expectDecodeOk "unit/decode/self" rawOpcode
          (.dictExt (.mutGet false false true .del)) },
    { name := "unit/decode/lower-neighbor"
      run := do
        expectDecodeOk "unit/decode/lower-neighbor" rawOpcodeLower
          (.dictExt (.mutGet false false false .del)) },
    { name := "unit/decode/upper-neighbor"
      run := do
        expectDecodeOk "unit/decode/upper-neighbor" rawOpcodeUpperNeighbor
          (.dictExt (.mutGet true false false .del)) },
    { name := "unit/decode/gap"
      run := do
        expectDecodeStepOrErr "unit/decode/gap" 0xf468 .invOpcode },
    { name := "unit/decode/truncated-8"
      run := do
        expectDecodeStepOrErr "unit/decode/truncated-8" 0xf4 .invOpcode },
    { name := "unit/assemble/invOpcode"
      run := do
        expectAssembleErr "unit/assemble/invOpcode" dictDelGetRefInstr .invOpcode }
  ]
  oracle := #[
    mkCase "ok/miss/null/key-0000" (stack3 (.slice (key4 0)) .null 4), -- [B6]
    mkCase "ok/miss/null/key-ffff" (stack3 (.slice (key4 15)) .null 4), -- [B6]
    mkCase "ok/miss/null/n0-empty" (stack3 (.slice key0) .null 0), -- [B6]
    mkCase "ok/miss/null/boundary-n1023" (stack3 (.slice key1023) .null 1023), -- [B6]
    mkCase "ok/miss/nonempty/single" (stack3 (.slice (key4 1)) (.cell dict4SingleRef) 4), -- [B6]
    mkCase "ok/miss/nonempty/two-a" (stack3 (.slice (key4 1)) (.cell dict4TwoRef) 4), -- [B6]
    mkCase "ok/miss/nonempty/two-b" (stack3 (.slice (key4 2)) (.cell dict4TwoRef) 4), -- [B6]
    mkCase "ok/miss/nonempty/three" (stack3 (.slice (key4 9)) (.cell dict4ThreeRef) 4), -- [B6]
    mkCase "ok/miss/nonempty/n8" (stack3 (.slice (key8 0x5A)) (.cell dict8SingleRef) 8), -- [B6]
    mkCase "ok/hit/single-ref-a" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRef) 4), -- [B7]
    mkCase "ok/hit/double-a" (stack3 (.slice (key4 0xA)) (.cell dict4TwoRef) 4), -- [B7]
    mkCase "ok/hit/double-b" (stack3 (.slice (key4 0xB)) (.cell dict4TwoRef) 4), -- [B7]
    mkCase "ok/hit/three-002" (stack3 (.slice (key4 0x2)) (.cell dict4ThreeRef) 4), -- [B7]
    mkCase "ok/hit/n0" (stack3 (.slice key0) (.cell dict0Ref) 0), -- [B7]
    mkCase "ok/hit/n8" (stack3 (.slice (key8 0xA5)) (.cell dict8SingleRef) 8), -- [B7]
    mkCase "ok/hit/miss-mismatch" (stack3 (.slice (key8 0x5A)) (.cell dict8SingleRef) 8), -- [B6]
    mkCase "err/underflow-0" #[], -- [B2]
    mkCase "err/underflow-1" #[intV 1], -- [B2]
    mkCase "err/underflow-2" #[intV 1, .cell dict4SingleRef], -- [B2]
    mkCase "err/n-too-large" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRef) 1024), -- [B3]
    mkCase "err/n-negative" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRef) (-1)), -- [B3]
    mkCase "err/n-nan" #[.slice (key4 0xA), .cell dict4SingleRef, .int .nan], -- [B3]
    mkCase "err/dict-type-int" (stack3 (.slice (key4 0xA)) (.int (.num 0)) 4), -- [B4]
    mkCase "err/dict-type-slice" (stack3 (.slice (key4 0xA)) (.slice key0) 4), -- [B4]
    mkCase "err/key-type-cell" (stack3 (.cell valueCellA) (.cell dict4SingleRef) 4), -- [B4]
    mkCase "err/key-type-null" (stack3 .null (.cell dict4SingleRef) 4), -- [B4]
    mkCase "err/key-short" (stack3 (.slice key1) (.cell dict4SingleRef) 4), -- [B5]
    mkCase "err/key-short-n0" (stack3 (.slice key1) (.cell dict4SingleRef) 0), -- [B5]
    mkCase "err/notref-struct" (stack3 (.slice (key4 0xA)) (.cell dict4SingleSlice) 4), -- [B8]
    mkCase "err/notref-bits" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRefBitsBad) 4), -- [B8]
    mkCase "err/notref-bits-only" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRefBitsOnly) 4), -- [B8]
    mkCase "err/notref-no-ref" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRefNoRef) 4), -- [B8]
    mkCase "err/notref-two-refs" (stack3 (.slice (key4 0xA)) (.cell dict4SingleRefTwoRefs) 4), -- [B8]
    mkCase "err/malformed-dict" (stack3 (.slice (key4 0xA)) (.cell malformedDict) 4), -- [B9]
    mkCase "err/malformed-keyroot" (stack3 (.slice (key8 0xA5)) (.cell malformedDict) 8), -- [B9]
    mkCase "gas/exact-null-miss" (stack3 (.slice key0) .null 0) (mkGasProgram dictDelGetRefBaseGas) dictDelGetRefGasExact, -- [B12]
    mkCase "gas/exact-minus-one" (stack3 (.slice key0) .null 0)
      (mkGasProgram dictDelGetRefBaseGasMinusOne) dictDelGetRefGasExactMinusOne, -- [B12]
    mkCase "gas/exact-boundary-n1023" (stack3 (.slice key1023) .null 1023)
      (mkGasProgram dictDelGetRefBaseGas) dictDelGetRefGasExact, -- [B12]
    mkCase "gas/exact-minus-one-boundary" (stack3 (.slice key1023) .null 1023)
      (mkGasProgram dictDelGetRefBaseGasMinusOne) dictDelGetRefGasExactMinusOne -- [B12]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictDelGetRefId
      count := 500
      gen := genDICTDELGETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTDELGETREF
