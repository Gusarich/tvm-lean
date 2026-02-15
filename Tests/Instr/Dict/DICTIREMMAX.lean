import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREMMAX

/-!
INSTRUCTION: DICTIREMMAX

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictDictGetMinMax` handles only `.dictGetMinMax` and delegates all others to `next`.

2. [B2] Runtime preamble / stack validation.
   - `checkUnderflow` requires both `n` and dictionary root values.
   - `popNatUpTo 257` validates key width and type/range for signed-int-key mode.

3. [B3] Empty/missing dictionary path.
   - `dictMinMaxWithCells none` returns `.ok none`, which skips deletion.
   - For remove-mode instructions (`args5=28`), `null` is pushed back as previous dict value before pushing `0`.

4. [B4] Dictionary miss vs hit.
   - A miss from non-empty root still takes the miss branch (`push old_dict`, `0`).
   - A hit proceeds through `(val, keyBits)` and goes into removal flow.

5. [B5] Remove-on-hit updates root.
   - On hit in remove mode, `dictDeleteWithCells` is invoked.
   - Deleting the only entry pushes `null`; deleting from larger dicts pushes a new dict root.

6. [B6] Value materialization for non-ref mode.
   - This opcode always pushes the found value as `slice`, never as raw cell, so no `.dictErr` by `byRef` check.

7. [B7] Integer key reconstruction.
   - `intKey` is true, `unsigned` is false, so `bitsToIntSignedTwos` reconstructs signed keys for `n=257`.
   - Boundary keys (e.g. `minInt257`, `-1`) and small keys must both behave correctly.

8. [B8] Assembler encoding / decode-valid args.
   - `.dictGetMinMax 28` is encodable as `0xF49C`.
   - Non-allowed args are rejected at assembly time.

9. [B9] Decoder behavior.
   - Family opcodes around `0xF49C` decode as neighboring `.dictGetMinMax` args.
   - Short/truncated streams decode as errors.

10. [B10] Gas accounting.
    - Exact base budget must succeed.
    - Base-minus-one must fail (OOG).
    - Removal on populated dictionaries must also account for `dictDeleteWithCells` `created` cells
      (`created * cellCreateGasPrice` surcharge).

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTIREMMAX" }

private def instr : Instr :=
  .dictGetMinMax 28

private def maxKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n true true with
  | .ok (some (_, keyBits), _) => some keyBits
  | _ => none

private def dictDeleteCreated (root : Cell) (n : Nat) : Nat :=
  match maxKeyBits root n with
  | some keyBits =>
      match dictDeleteWithCells (some root) keyBits with
      | .ok (_, _, created, _) => created
      | .error _ => 0
  | none => 0

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC 8) #[]
private def badValueSlice : Slice := mkSliceFromBits (natToBits 0xF0 8)

private def dictNull : Value := .null
private def dictSingleRef8 : Cell :=
  mkDictSetRefRoot! "dictSingleRef8" 8 #[(5, valueA)]
private def dictTwoRef8 : Cell :=
  mkDictSetRefRoot! "dictTwoRef8" 8 #[(5, valueA), (-1, valueB)]
private def dictThreeRef8 : Cell :=
  mkDictSetRefRoot! "dictThreeRef8" 8 #[(0, valueA), (1, valueB), (-1, valueC)]
private def dictSingleRef257 : Cell :=
  mkDictSetRefRoot! "dictSingleRef257" 257 #[(0, valueA)]
private def dictTwoRef257 : Cell :=
  mkDictSetRefRoot! "dictTwoRef257" 257 #[(minInt257, valueA), (0, valueB)]
private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(7, badValueSlice)]
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def twoRef8Created : Nat := dictDeleteCreated dictTwoRef8 8
private def twoRef8Penalty : Int := Int.ofNat twoRef8Created * cellCreateGasPrice
private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def removeTwoRef8Gas : Int := baseGas + twoRef8Penalty
private def removeTwoRef8GasMinusOne : Int := if removeTwoRef8Gas > 0 then removeTwoRef8Gas - 1 else 0

private def rawOpcodeF49C : Cell := Cell.mkOrdinary (natToBits 0xF49C 16) #[]
private def rawOpcodeF49B : Cell := Cell.mkOrdinary (natToBits 0xF49B 16) #[]
private def rawOpcodeF49D : Cell := Cell.mkOrdinary (natToBits 0xF49D 16) #[]
private def rawOpcodeF49E : Cell := Cell.mkOrdinary (natToBits 0xF49E 16) #[]
private def rawOpcodeF49F : Cell := Cell.mkOrdinary (natToBits 0xF49F 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

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

private def mkCodeCase
    (name : String)
    (stack : Array Value := #[])
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV 909)) stack

private def genDictIremMaxCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/null-n0" (#[dictNull, intV 0]), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/null-n8" (#[dictNull, intV 8]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/null-n257" (#[dictNull, intV 257]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/single-ref8" (#[ .cell dictSingleRef8, intV 8 ]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/two-ref8" (#[ .cell dictTwoRef8, intV 8 ]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/three-ref8" (#[ .cell dictThreeRef8, intV 8 ]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/single-ref257" (#[ .cell dictSingleRef8, intV 257 ]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/two-ref257" (#[ .cell dictTwoRef257, intV 257 ]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/slice-value" (#[ .cell dictSliceSingle8, intV 8 ]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/type-top-int" (#[ .cell valueA, intV 8 ]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/type-top-tuple" (#[ .tuple #[], intV 8 ]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type-key-nan" (#[ .cell dictSingleRef8, (.int .nan) ]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/n-1" (#[ .cell dictSingleRef8, intV (-1) ]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/n-258" (#[ .cell dictSingleRef8, intV 258 ]), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/root-non-dict-cell" (#[ .cell malformedDict, intV 8 ]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/gas/exact" (#[ dictNull, intV 8])
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 17 then
      (mkCase "fuzz/gas/exact-minus-one" (#[ dictNull, intV 8])
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 18 then
      (mkCase "fuzz/gas/removed-two-ref8" (#[ .cell dictTwoRef8, intV 8 ])
        (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 19 then
      (mkCase "fuzz/gas/removed-two-ref8-oog" (#[ .cell dictTwoRef8, intV 8 ])
        (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr]), rng1)
    else
      (mkCodeCase "fuzz/raw/f49d" #[.cell dictSingleRef8, intV 8] rawOpcodeF49D, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "dispatch/fallback"
          (runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV 909)) (#[intV 1, intV 2]))
          #[intV 1, intV 2, intV 909] },
    { name := "unit/opcode/assemble/exact" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF49C 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF49C bits, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTIREMMAX failed: {reprStr e}") },
    { name := "unit/opcode/assemble/reject-oob-args" -- [B8]
      run := do
        match assembleCp0 [.dictGetMinMax 1] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted out-of-range args=1")
        | .error _ => pure () },
    { name := "unit/decode/branches" -- [B9]
      run := do
        let s0 := Slice.ofCell (Cell.mkOrdinary (rawOpcodeF49B.bits ++ rawOpcodeF49C.bits ++ rawOpcodeF49D.bits ++ rawOpcodeF49E.bits) #[])
        let s1 ← expectDecodeStep "decode/prev" s0 (.dictGetMinMax 27) 16
        let s2 ← expectDecodeStep "decode/self" s1 (.dictGetMinMax 28) 16
        let s3 ← expectDecodeStep "decode/next" s2 (.dictGetMinMax 29) 16
        let s4 ← expectDecodeStep "decode/nextnext" s3 (.dictGetMinMax 30) 16
        if s4.bitsRemaining + s4.refsRemaining != 0 then
          throw (IO.userError "decode did not consume full stream") },
    { name := "unit/decode/truncated-or-invalid" -- [B9]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode") }
  ]
  oracle := #[
    mkCase "ok/miss/null/0" (#[dictNull, intV 0]), -- [B3][B4]
    mkCase "ok/miss/null/8" (#[dictNull, intV 8]), -- [B3][B4]
    mkCase "ok/miss/null/257" (#[dictNull, intV 257]), -- [B3][B4]
    mkCase "ok/hit/single-ref8" (#[ .cell dictSingleRef8, intV 8 ]), -- [B4][B5][B6][B7]
    mkCase "ok/hit/single-ref8-alt" (#[ .cell dictSingleRef8, intV 5 ]), -- [B4][B5][B6][B7]
    mkCase "ok/hit/single-ref8-slice" (#[ .cell dictSliceSingle8, intV 8 ]), -- [B6]
    mkCase "ok/hit/single-ref257-zero" (#[ .cell dictSingleRef257, intV 257 ]), -- [B4][B5][B7]
    mkCase "ok/hit/single-ref257-min" (#[ .cell dictSingleRef257, intV 257 ]), -- [B4][B5][B7]
    mkCase "ok/hit/two-ref8" (#[ .cell dictTwoRef8, intV 8 ]), -- [B4][B5][B6][B7]
    mkCase "ok/hit/two-ref8-alt-n1" (#[ .cell dictTwoRef8, intV 1 ]), -- [B4][B5][B6][B7]
    mkCase "ok/hit/three-ref8" (#[ .cell dictThreeRef8, intV 8 ]), -- [B4][B5][B6][B7]
    mkCase "ok/hit/two-ref257" (#[ .cell dictTwoRef257, intV 257 ]), -- [B4][B5][B7]
    mkCodeCase "ok/code/raw/f49c" (#[dictNull, intV 8]) rawOpcodeF49C, -- [B9]
    mkCodeCase "ok/code/raw/f49b" (#[dictNull, intV 8]) rawOpcodeF49B, -- [B9]
    mkCodeCase "ok/code/raw/f49d" (#[dictNull, intV 8]) rawOpcodeF49D, -- [B9]
    mkCodeCase "ok/code/raw/f49e" (#[dictNull, intV 8]) rawOpcodeF49E, -- [B9]
    mkCase "err/underflow/empty" (#[]), -- [B2]
    mkCase "err/underflow/one-item" (#[dictNull]), -- [B2]
    mkCase "err/underflow/two-items" (#[dictNull, intV 8]), -- [B2]
    mkCase "err/type/top-int" (#[ .cell valueA, intV 8 ]), -- [B2]
    mkCase "err/type/top-tuple" (#[ .tuple #[], intV 8 ]), -- [B2]
    mkCase "err/type/key-non-int" (#[ .cell dictSingleRef8, .slice badValueSlice ]), -- [B2]
    mkCase "err/type/key-nan" (#[ .cell dictSingleRef8, .int .nan ]), -- [B2]
    mkCase "err/n/negative" (#[ .cell dictSingleRef8, intV (-1) ]), -- [B2]
    mkCase "err/n/too-large" (#[ .cell dictSingleRef8, intV 258 ]), -- [B2]
    mkCase "err/n/too-large-257-1" (#[ .cell dictSingleRef8, intV 258 ]), -- [B2]
    mkCase "err/root-non-dict-cell" (#[ .cell malformedDict, intV 8 ]), -- [B2][B5]
    mkCase "err/mismatch-n-width" (#[ .cell dictSingleRef8, intV 256 ]), -- [B2]
    mkCase "err/mismatch-n-width-alt" (#[ .cell dictSingleRef257, intV 8 ]), -- [B2]
    mkCase "gas/exact/base-miss" (#[dictNull, intV 8])
      #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr] -- [B10]
      (gasLimits := oracleGasLimitsExact baseGas),
    mkCase "gas/exact-minus-one-miss" (#[dictNull, intV 8])
      #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr] -- [B10]
      (gasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne),
    mkCase "gas/removed-two-ref8" (#[ .cell dictTwoRef8, intV 8 ])
      #[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact removeTwoRef8Gas), -- [B5][B10]
    mkCase "gas/removed-two-ref8-oog" (#[ .cell dictTwoRef8, intV 8 ])
      #[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact removeTwoRef8GasMinusOne), -- [B5][B10]
    mkCase "ok/program/trimmed-stack" (#[ .cell dictSingleRef8, intV 8]) (#[instr, .pushInt (.num 777)]), -- [B5]
    mkCodeCase "err/raw/truncated8" #[] rawTruncated8, -- [B9]
    mkCase "ok/raw/neighbor-chain" (#[ .cell dictSingleRef8, intV 8 ]) (#[.dictGetMinMax 28]) -- [B9]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictIremMaxCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREMMAX
