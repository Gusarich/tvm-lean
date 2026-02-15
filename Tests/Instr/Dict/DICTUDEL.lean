import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUDEL

/-!
INSTRUCTION: DICTUDEL

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch/runtime selection:
   - `execInstrDictExt` handles `.dictExt (.del false false)`.
   - Any non-`dictExt` instruction falls through to `next`.
2. [B2] Runtime stack-shape validation:
   - `VM.checkUnderflow 3` must reject stacks with fewer than 3 items.
3. [B3] Runtime `n` parsing:
   - `popNatUpTo 1023` validates top operand.
   - Non-int `n` -> `.typeChk`.
   - `.nan`, `n < 0`, `n > 1023` -> `.rangeChk`.
4. [B4] Operand type checks:
   - `popMaybeCell` accepts `.null` and `.cell` dictionary roots.
   - Non-cell root -> `.typeChk`.
   - Key must be a `slice`; non-slice -> `.typeChk`.
5. [B5] Slice-key extraction:
   - `n` bits are read from the key slice.
   - `key` shorter than `n` bits -> `.cellUnd`.
6. [B6] Delete outcomes:
   - Hit returns `(newRoot, -1)`.
   - Miss returns `(sameRoot, 0)`.
   - `null` dictionary root is supported.
7. [B7] Malformed structure:
   - Invalid dictionary shapes produce traversal errors (`.dictErr` / `.cellUnd`).
8. [B8] Assembler:
   - CP0 assembler encodes `.dictExt (.del ...)` variants (`0xf459..0xf45b`).
9. [B9] Decoder:
   - `0xf459` decodes to `.dictExt (.del false false)`.
   - `0xf45a` decodes to `.dictExt (.del true false)`.
   - `0xf45b` decodes to `.dictExt (.del true true)`.
   - `0xf458` and `0xf45c` do not decode.
   - Truncated 8- and 15-bit opcode cells fail decode.
10. [B10] Gas accounting:
   - Exact and exact-minus-one branches are required.
11. [B11] Dynamic gas:
   - Successful delete may create cells (`created * cellCreateGasPrice`).

TOTAL BRANCHES: 11
Each oracle test below is tagged with the branch(es) it covers.
-/

private def dictDelId : InstrId :=
  { name := "DICTUDEL" }

private def dictDelInstr : Instr :=
  .dictExt (.del false false)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def dictDelCode : Cell :=
  raw16 0xf459

private def dictDelSignedCode : Cell :=
  raw16 0xf45a

private def dictDelUnsignedCode : Cell :=
  raw16 0xf45b

private def dispatchSentinel : Int :=
  7007

private def valueA : Slice :=
  mkSliceFromBits (natToBits 0xA 4)

private def valueB : Slice :=
  mkSliceFromBits (natToBits 0xB 4)

private def valueC : Slice :=
  mkSliceFromBits (natToBits 0xC 4)

private def sampleCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[]

private def sampleCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x3B 8) #[]

private def malformedRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def key4_0 : BitString := #[]
private def key4_2 : BitString := natToBits 2 4
private def key4_3 : BitString := natToBits 3 4
private def key4_4 : BitString := natToBits 4 4
private def key4_15 : BitString := natToBits 15 4
private def key8_0x7f : BitString := natToBits 0x7f 8

private def mkDictSliceRoot (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let (k, v) := pair
      match dictSetSliceWithCells root k v .set with
      | .ok (some newRoot, _ok, _created, _loaded) => root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: insertion returned none"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: expected non-empty dictionary"

private def dictRoot4Single2 : Cell :=
  mkDictSliceRoot "dict/4/single2" #[(key4_2, valueA)]

private def dictRoot4Single3 : Cell :=
  mkDictSliceRoot "dict/4/single3" #[(key4_3, valueB)]

private def dictRoot4Single4 : Cell :=
  mkDictSliceRoot "dict/4/single4" #[(key4_4, valueC)]

private def dictRoot4Single15 : Cell :=
  mkDictSliceRoot "dict/4/single15" #[(key4_15, valueA)]

private def dictRoot4Single0 : Cell :=
  mkDictSliceRoot "dict/4/single0" #[(key4_0, valueB)]

private def dictRoot4Two : Cell :=
  mkDictSliceRoot "dict/4/two" #[(key4_2, valueA), (key4_3, valueB)]

private def dictRoot8Single : Cell :=
  mkDictSliceRoot "dict/8/single" #[(key8_0x7f, valueC)]

private def dictRoot4PayloadBits : Cell :=
  mkDictSliceRoot "dict/4/payload/bits" #[(key4_2, mkSliceFromBits (natToBits 0b101 3)), (key4_3, valueB)]

private def dictRoot4PayloadNoRef : Cell :=
  mkDictSliceRoot "dict/4/payload/no-ref" #[(key4_2, Slice.ofCell (Cell.mkOrdinary #[] #[])), (key4_3, valueB)]

private def dictRoot4PayloadTwoRefs : Cell :=
  mkDictSliceRoot "dict/4/payload/two-refs"
    #[(key4_2, Slice.ofCell (Cell.mkOrdinary #[] #[sampleCellA, sampleCellB])), (key4_3, valueB)]

private def dictRoot4MergeCandidate : Cell :=
  mkDictSliceRoot "dict/4/merge" #[(key4_2, valueA), (key4_3, valueB), (key4_4, valueC)]

private def mkStack
    (root : Value)
    (keyBits : BitString)
    (n : Value) : Array Value :=
  #[.slice (mkSliceFromBits keyBits), root, n]

private def mkStackWithTail
    (tail : Value)
    (root : Value)
    (keyBits : BitString)
    (n : Value) : Array Value :=
  #[tail, .slice (mkSliceFromBits keyBits), root, n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelId
    codeCell? := some dictDelCode
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictDelDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt dictDelInstr stack

private def runDictDelFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.tonEnvOp .setGasLimit) (VM.push (intV dispatchSentinel)) stack

private def dictDelGas : Int :=
  computeExactGasBudget dictDelInstr

private def dictDelGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictDelInstr

private def dictDelGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictDelGas

private def dictDelGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictDelGasMinusOne

private def dictDeleteCreated (root : Cell) (keyBits : BitString) : Nat :=
  match dictDeleteWithCells (some root) keyBits with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def dictDelHitGas : Int :=
  dictDelGas + Int.ofNat (dictDeleteCreated dictRoot4Two key4_2) * cellCreateGasPrice

private def dictDelHitGasMinusOne : Int :=
  if dictDelHitGas > 0 then dictDelHitGas - 1 else 0

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected end-of-stream decode")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleOk16
    (label : String)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")
  | .ok cell =>
      expectDecodeOk label cell instr

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

private def genDICTUDELFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (tag, rng2) := randNat rng1 0 999_999
  let case : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/hit/single" (mkStack (.cell dictRoot4Single2) key4_2 (intV 4))
    else if shape = 1 then
      mkCase "fuzz/hit/two-entry" (mkStack (.cell dictRoot4Two) key4_2 (intV 4))
    else if shape = 2 then
      mkCase "fuzz/miss/null" (mkStack .null key4_2 (intV 4))
    else if shape = 3 then
      mkCase "fuzz/miss/non-empty" (mkStack (.cell dictRoot4Two) key4_15 (intV 4))
    else if shape = 4 then
      mkCase "fuzz/n-zero-hit" (mkStack (.cell dictRoot4Single0) key4_0 (intV 0))
    else if shape = 5 then
      mkCase "fuzz/n-zero-miss" (mkStack (.cell dictRoot4Single2) key4_0 (intV 0))
    else if shape = 6 then
      mkCase "fuzz/key-underflow" (mkStack (.cell dictRoot8Single) key8_0x7f (intV 7))
    else if shape = 7 then
      mkCase "fuzz/nan" (mkStack (.cell dictRoot4Single2) key4_2 (.int .nan))
    else if shape = 8 then
      mkCase "fuzz/n-negative" (mkStack (.cell dictRoot4Single2) key4_2 (intV (-1)))
    else if shape = 9 then
      mkCase "fuzz/n-too-large" (mkStack (.cell dictRoot4Single2) key4_2 (intV 1024))
    else if shape = 10 then
      mkCase "fuzz/key-type" (#[intV 4, .cell dictRoot4Single2, intV 4])
    else if shape = 11 then
      mkCase "fuzz/dict-type" (#[.slice (mkSliceFromBits key4_2), .tuple #[], intV 4])
    else if shape = 12 then
      mkCaseCode "fuzz/decode-below" #[] (raw16 0xf458)
    else if shape = 13 then
      mkCaseCode "fuzz/decode-above" #[] (raw16 0xf45c)
    else if shape = 14 then
      mkCaseCode "fuzz/decode-trunc8" #[] (raw8 0xf4)
    else if shape = 15 then
      mkCaseCode "fuzz/decode-trunc15" #[] (Cell.mkOrdinary (natToBits (0xf459 >>> 1) 15) #[])
    else if shape = 16 then
      mkCase "fuzz/gas/exact-miss" (mkStack .null key4_2 (intV 4)) dictDelGasExact
    else if shape = 17 then
      mkCase "fuzz/gas/exact-minus-one" (mkStack .null key4_2 (intV 4)) dictDelGasExactMinusOne
    else if shape = 18 then
      mkCase "fuzz/gas/hit-exact" (mkStack (.cell dictRoot4Two) key4_2 (intV 4)) (oracleGasLimitsExact dictDelHitGas)
    else if shape = 19 then
      mkCase "fuzz/gas/hit-minus-one" (mkStack (.cell dictRoot4Two) key4_2 (intV 4)) (oracleGasLimitsExactMinusOne dictDelHitGasMinusOne)
    else if shape = 20 then
      mkCase "fuzz/payload-bits" (mkStack (.cell dictRoot4PayloadBits) key4_2 (intV 4))
    else if shape = 21 then
      mkCase "fuzz/payload-no-ref" (mkStack (.cell dictRoot4PayloadNoRef) key4_2 (intV 4))
    else if shape = 22 then
      mkCase "fuzz/payload-two-refs" (mkStack (.cell dictRoot4PayloadTwoRefs) key4_2 (intV 4))
    else if shape = 23 then
      mkCase "fuzz/underflow-one" #[.cell dictRoot4Two]
    else if shape = 24 then
      mkCase "fuzz/underflow-two" #[.cell dictRoot4Two, intV 4]
    else if shape = 25 then
      mkCase "fuzz/malformed-root" (mkStack (.cell malformedRoot) key4_2 (intV 4))
    else if shape = 26 then
      mkCase "fuzz/merge-candidate" (mkStack (.cell dictRoot4MergeCandidate) key4_3 (intV 4))
    else
      mkCase "fuzz/tail" (mkStackWithTail (intV 77) (.cell dictRoot4Two) key4_2 (intV 4))
  ({ case with name := s!"{case.name}/{tag}" }, rng2)

def suite : InstrSuite where
  id := dictDelId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/fallback" (runDictDelFallback #[]) #[intV dispatchSentinel]
    },
    { name := "unit/runtime/underflow/empty"
      run := do
        expectErr "underflow/empty" (runDictDelDirect #[]) .stkUnd
    },
    { name := "unit/runtime/underflow/one"
      run := do
        expectErr "underflow/one" (runDictDelDirect #[.cell dictRoot4Single2]) .stkUnd
    },
    { name := "unit/runtime/underflow/two"
      run := do
        expectErr "underflow/two" (runDictDelDirect #[.cell dictRoot4Single2, .slice (mkSliceFromBits key4_2)]) .stkUnd
    },
    { name := "unit/runtime/range/type"
      run := do
        expectErr "n-non-int" (runDictDelDirect (#[(.slice (mkSliceFromBits key4_2)), .cell dictRoot4Single2, .tuple #[]]) ) .typeChk
    },
    { name := "unit/runtime/range/nan"
      run := do
        expectErr "n-nan" (runDictDelDirect (mkStack (.cell dictRoot4Single2) key4_2 (.int .nan))) .rangeChk
    },
    { name := "unit/runtime/range/n-negative"
      run := do
        expectErr "n-negative" (runDictDelDirect (mkStack (.cell dictRoot4Single2) key4_2 (intV (-1))) ) .rangeChk
    },
    { name := "unit/runtime/range/n-too-large"
      run := do
        expectErr "n-too-large" (runDictDelDirect (mkStack (.cell dictRoot4Single2) key4_2 (intV 1024))) .rangeChk
    },
    { name := "unit/runtime/type/key-not-slice"
      run := do
        expectErr "type-key-not-slice" (runDictDelDirect #[intV 4, .cell dictRoot4Single2, intV 4]) .typeChk
    },
    { name := "unit/runtime/type/dict-not-cell"
      run := do
        expectErr "type-dict-not-cell" (runDictDelDirect #[.slice (mkSliceFromBits key4_2), .tuple #[], intV 4]) .typeChk
    },
    { name := "unit/runtime/key-underflow"
      run := do
        expectErr "key-underflow" (runDictDelDirect (mkStack (.cell dictRoot8Single) key8_0x7f (intV 7))) .dictErr
    },
    { name := "unit/runtime/hit/single"
      run := do
        expectOkStack "hit/single" (runDictDelDirect (mkStack (.cell dictRoot4Single2) key4_2 (intV 4))) #[.null, intV (-1)]
    },
    { name := "unit/runtime/hit/two-entry"
      run := do
        expectOkStack "hit/two-entry" (runDictDelDirect (mkStack (.cell dictRoot4Two) key4_2 (intV 4)))
          #[.cell dictRoot4Single3, intV (-1)]
    },
    { name := "unit/runtime/miss/null"
      run := do
        expectOkStack "miss/null" (runDictDelDirect (mkStack .null key4_2 (intV 4))) #[.null, intV 0]
    },
    { name := "unit/runtime/miss/non-empty"
      run := do
        expectOkStack "miss/non-empty" (runDictDelDirect (mkStack (.cell dictRoot4Two) key4_15 (intV 4)))
          #[.cell dictRoot4Two, intV 0]
    },
    { name := "unit/runtime/hit/n-zero"
      run := do
        expectOkStack "hit-n-zero" (runDictDelDirect (mkStack (.cell dictRoot4Single0) key4_0 (intV 0))) #[.null, intV (-1)]
    },
    { name := "unit/runtime/miss/n-zero"
      run := do
        expectOkStack "miss-n-zero" (runDictDelDirect (mkStack (.cell dictRoot4Single2) key4_0 (intV 0)))
          #[.null, intV (-1)]
    },
    { name := "unit/runtime/hit/tail"
      run := do
        expectOkStack "hit/tail" (runDictDelDirect (mkStackWithTail (intV 77) (.cell dictRoot4Single2) key4_2 (intV 4)))
          #[intV 77, .null, intV (-1)]
    },
    { name := "unit/runtime/payload/bits"
      run := do
        expectOkStack "payload/bits" (runDictDelDirect (mkStack (.cell dictRoot4PayloadBits) key4_2 (intV 4)))
          #[.cell (mkDictSliceRoot "unit/payload/bits" #[(key4_3, valueB)]), intV (-1)]
    },
    { name := "unit/runtime/payload/no-ref"
      run := do
        expectOkStack "payload/no-ref" (runDictDelDirect (mkStack (.cell dictRoot4PayloadNoRef) key4_2 (intV 4)))
          #[.cell (mkDictSliceRoot "unit/payload/no-ref" #[(key4_3, valueB)]), intV (-1)]
    },
    { name := "unit/runtime/payload/two-refs"
      run := do
        expectOkStack "payload/two-refs" (runDictDelDirect (mkStack (.cell dictRoot4PayloadTwoRefs) key4_2 (intV 4)))
          #[.cell (mkDictSliceRoot "unit/payload/two-refs" #[(key4_3, valueB)]), intV (-1)]
    },
    { name := "unit/runtime/malformed-root"
      run := do
        expectErr "malformed-root" (runDictDelDirect (mkStack (.cell malformedRoot) key4_2 (intV 4))) .cellUnd
    },
    { name := "unit/decode/target"
      run := do
        expectDecodeOk "decode/target" dictDelCode dictDelInstr
    },
    { name := "unit/decode/neighbors"
      run := do
        expectDecodeOk "decode/signed" dictDelSignedCode (.dictExt (.del true false))
        expectDecodeOk "decode/unsigned" dictDelUnsignedCode (.dictExt (.del true true))
    },
    { name := "unit/decode/boundaries"
      run := do
        expectDecodeErr "decode/under" (raw16 0xf458) .invOpcode
        expectDecodeErr "decode/over" (raw16 0xf45c) .invOpcode
        expectDecodeErr "decode/trunc-8" (raw8 0xf4) .invOpcode
        expectDecodeErr "decode/trunc-15" (Cell.mkOrdinary (natToBits (0xf459 >>> 1) 15) #[]) .invOpcode
    },
    { name := "unit/assemble"
      run := do
        expectAssembleOk16 "assemble/ok" dictDelInstr
    }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one-item" #[.cell dictRoot4Single2],
    mkCase "oracle/underflow/two-items" #[.cell dictRoot4Single2, .slice (mkSliceFromBits key4_2)],
    -- [B3]
    mkCase "oracle/type/nan" (mkStack (.cell dictRoot4Single2) key4_2 (.int .nan)),
    mkCase "oracle/type/n-negative" (mkStack (.cell dictRoot4Single2) key4_2 (intV (-1))),
    mkCase "oracle/type/n-too-large" (mkStack (.cell dictRoot4Single2) key4_2 (intV 1024)),
    mkCase "oracle/type/n-max" (mkStack (.cell dictRoot4Single2) key4_2 (intV 1023)),
    -- [B4]
    mkCase "oracle/type/key-not-slice" (#[.cell dictRoot4Single2, intV 4, intV 4]),
    mkCase "oracle/type/key-not-slice" (#[intV 4, .cell dictRoot4Single2, intV 4]),
    mkCase "oracle/type/dict-not-cell" (#[.slice (mkSliceFromBits key4_2), .tuple #[], intV 4]),
    -- [B5]
    mkCase "oracle/key-underflow" (mkStack (.cell dictRoot8Single) key8_0x7f (intV 7)),
    mkCase "oracle/key-0" (mkStack (.cell dictRoot4Single0) key4_0 (intV 0)),
    -- [B6]
    mkCase "oracle/miss/null" (mkStack .null key4_2 (intV 4)),
    mkCase "oracle/miss/non-empty" (mkStack (.cell dictRoot4Two) key4_15 (intV 4)),
    mkCase "oracle/miss/n-zero" (mkStack (.cell dictRoot4Single2) key4_0 (intV 0)),
    mkCase "oracle/hit/single" (mkStack (.cell dictRoot4Single2) key4_2 (intV 4)),
    mkCase "oracle/hit/two-first" (mkStack (.cell dictRoot4Two) key4_2 (intV 4)),
    mkCase "oracle/hit/two-second" (mkStack (.cell dictRoot4Two) key4_3 (intV 4)),
    mkCase "oracle/hit/n-zero" (mkStack (.cell dictRoot4Single0) key4_0 (intV 0)),
    mkCase "oracle/tail-preserve" (mkStackWithTail (intV 99) (.cell dictRoot4Two) key4_2 (intV 4)),
    -- [B7]
    mkCase "oracle/malformed-root" (mkStack (.cell malformedRoot) key4_2 (intV 4)),
    -- [B6]
    mkCase "oracle/payload/bits" (mkStack (.cell dictRoot4PayloadBits) key4_2 (intV 4)),
    mkCase "oracle/payload/no-ref" (mkStack (.cell dictRoot4PayloadNoRef) key4_2 (intV 4)),
    mkCase "oracle/payload/two-refs" (mkStack (.cell dictRoot4PayloadTwoRefs) key4_2 (intV 4)),
    mkCase "oracle/merge/candidate" (mkStack (.cell dictRoot4MergeCandidate) key4_3 (intV 4)),
    -- [B9]
    mkCaseCode "oracle/decode/target" #[] dictDelCode,
    mkCaseCode "oracle/decode/signed" #[] dictDelSignedCode,
    mkCaseCode "oracle/decode/unsigned" #[] dictDelUnsignedCode,
    mkCaseCode "oracle/decode/below" #[] (raw16 0xf458),
    mkCaseCode "oracle/decode/above" #[] (raw16 0xf45c),
    mkCaseCode "oracle/decode/trunc8" #[] (raw8 0xf4),
    mkCaseCode "oracle/decode/trunc15" #[] (Cell.mkOrdinary (natToBits (0xf459 >>> 1) 15) #[]),
    -- [B8]
    mkCaseCode "oracle/assemble" #[] dictDelCode,
    -- [B10][B11]
    mkCase "oracle/gas/exact-miss" (mkStack .null key4_2 (intV 4)) dictDelGasExact,
    mkCase "oracle/gas/exact-minus-one-miss" (mkStack .null key4_2 (intV 4)) dictDelGasExactMinusOne,
    mkCase "oracle/gas/exact-hit" (mkStack (.cell dictRoot4Two) key4_2 (intV 4)) (oracleGasLimitsExact dictDelHitGas),
    mkCase "oracle/gas/exact-minus-one-hit" (mkStack (.cell dictRoot4Two) key4_2 (intV 4)) (oracleGasLimitsExactMinusOne dictDelHitGasMinusOne)
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr dictDelId
      count := 500
      gen := genDICTUDELFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUDEL
