import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUSET

/-!
INSTRUCTION: DICTUSET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictDictSet` handles only `.dictSet`; all other opcodes are delegated to `next`.
   - Verified with explicit fallback test and opcode-family dispatch.

2. [B2] Stack arity guard.
   - `checkUnderflow 4` is always executed first.
   - 0..3 stack elements must produce `.stkUnd` before any semantic checks.

3. [B3] Width (`n`) parsing and validation.
   - `popNatUpTo 1023` accepts finite values in `[0,1023]` only.
   - `.nan` and out-of-range values (`< 0` or `> 1023`) raise `.rangeChk`.

4. [B4] Root argument shape.
   - `popMaybeCell` accepts only `.null` and `.cell`.
   - Tuple/other values raise `.typeChk`.

5. [B5] Unsigned integer key conversion.
   - With `intKey=true`, `unsigned=true`, keys are converted via `dictKeyBits? idx n true`.
   - `n = 0` accepts only key `0`.
   - For `n > 0`, any negative key or key `>= 2^n` is rejected as `.rangeChk`.

6. [B6] Key-value type compatibility.
   - New value must be `.slice` for `byRef=false`.
   - Wrong value type raises `.typeChk`.

7. [B7] Dictionary mutation semantics.
   - `.set` performs update/insert via `dictSetSliceWithCells ... .set`.
   - Result is pushed as `.cell` for non-empty root or `.null` for empty.
   - `mode == .set` checks helper success (`ok`); if false, Lean throws `.fatal`.

8. [B8] Malformed dictionary structure and lookup bookkeeping.
   - Structural failures in `dictSetSliceWithCells` propagate as `.dictErr`/other interpreter errors.
   - Loaded cells are still registered on error paths.

9. [B9] Assembler encoding/decoder + opcode boundaries.
   - Valid assembly for DICTUSET is exactly opcode `0xF416`.
   - `.dictSet false true false .set` is invalid and must encode as `.invOpcode`.
   - Decoder accepts set opcodes `0xF412..0xF417` and rejects adjacent invalid boundaries (`0xF411`, `0xF418`) and truncated forms.

10. [B10] Gas accounting.
    - Gas = `computeExactGasBudget instr + created * cellCreateGasPrice`.
    - Deterministic miss/hit cases should pass exact gas and fail at exact-minus-one.

TOTAL BRANCHES: 10
- [B1] dispatch
- [B2] underflow
- [B3] n validation
- [B4] root shape/type
- [B5] unsigned key conversion
- [B6] value typing
- [B7] set semantics
- [B8] malformed-root failure path
- [B9] encoding/decoding
- [B10] gas behavior
-/

private def suiteId : InstrId :=
  { name := "DICTUSET" }

private def instr : Instr := .dictSet true true false .set

private def dispatchSentinel : Int :=
  13_021

private def opcode16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw412 : Cell := opcode16 0xF412
private def raw413 : Cell := opcode16 0xF413
private def raw414 : Cell := opcode16 0xF414
private def raw415 : Cell := opcode16 0xF415
private def raw416 : Cell := opcode16 0xF416
private def raw417 : Cell := opcode16 0xF417
private def raw411 : Cell := opcode16 0xF411
private def raw418 : Cell := opcode16 0xF418
private def rawF4 : Cell := opcode16 0xF4

private def opcodeSlice16 (w : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w 16) #[])

private def sampleSliceA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def sampleSliceB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def sampleSliceC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def sampleSliceD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def sampleSliceE : Slice := mkSliceFromBits (natToBits 0xE5 8)
private def sampleSliceF : Slice := mkSliceFromBits (natToBits 0xF6 8)

private def sampleCellA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def sampleCellB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]

private def malformedDictCell : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def requireBits (label : String) (key : Int) (n : Nat) : BitString :=
  match dictKeyBits? key n true with
  | some bits => bits
  | none => panic! s!"{label}: key out of range (key={key}, n={n})"

private def mkDictSetRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    entries.foldl
      (fun st e =>
        let (k, v) := e
        match st with
        | some root =>
            match dictSetSliceWithCells (some root) (requireBits label k n) v .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            match dictSetSliceWithCells none (requireBits label k n) v .set with
            | .ok (some next, _, _, _) => some next
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to construct dictionary"

private def mkDictIntExpected! (label : String) (root : Option Cell) (n : Nat) (key : Int) (value : Slice) : Cell :=
  match dictSetSliceWithCells root (requireBits label key n) value .set with
  | .ok (some next, _, _, _) => next
  | .ok (none, _, _, _) => panic! s!"{label}: expected root, got none"
  | .error e => panic! s!"{label}: dict set failed ({reprStr e})"

private def mkDictIntCreated (label : String) (root : Option Cell) (n : Nat) (key : Int) (value : Slice) : Nat :=
  match dictSetSliceWithCells root (requireBits label key n) value .set with
  | .ok (_, _, created, _) => created
  | .error e => panic! s!"{label}: dict set failed ({reprStr e})"

private def dictUSetExpected! (root : Option Cell) (n : Nat) (key : Int) (value : Slice) : Cell :=
  mkDictIntExpected! "DICTUSET expected" root n key value

private def dictUSetCreated (root : Option Cell) (n : Nat) (key : Int) (value : Slice) : Nat :=
  mkDictIntCreated "DICTUSET created" root n key value

private def dictUSet8Root : Cell :=
  mkDictSetRoot! "dictUSet8Root" 8 #[(0, sampleSliceA), (5, sampleSliceB), (7, sampleSliceC)]

private def dictUSet8ReplA : Cell :=
  mkDictSetRoot! "dictUSet8ReplA" 8 #[(0, sampleSliceA), (5, sampleSliceD), (7, sampleSliceC)]

private def dictUSet0Root : Cell :=
  mkDictSetRoot! "dictUSet0Root" 0 #[(0, sampleSliceA)]

private def dictUSet0Repl : Cell :=
  mkDictSetRoot! "dictUSet0Repl" 0 #[(0, sampleSliceB)]

private def dictUSet1023Root : Cell :=
  mkDictSetRoot! "dictUSet1023Root" 1023 #[(0, sampleSliceD), (1, sampleSliceE)]

private def runDICTUSET (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def runDICTUSETFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    initStack := stack
    program := program
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    initStack := stack
    instr := suiteId
    codeCell? := some code
    gasLimits := gasLimits
    fuel := fuel }

private def mkStack (value : Slice) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[(.slice value), .int (.num key), dict, intV n]

private def mkGasProgram (gas : Int) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]

private def expectDecodeStep (label : String) (s : Slice) (expected : Instr) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (i, bits, rest) =>
      if i != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {reprStr i}")
      if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      pure rest

private def expectAssembleEq (label : String) (code : Cell) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      if c.bits != code.bits then
        throw (IO.userError s!"{label}: expected {code.bits}, got {c.bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected assembly success, got {e}")

private def expectAssembleInv (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok c =>
      throw (IO.userError s!"{label}: expected invOpcode, got bits {c.bits}")

private def expectDecodeInv (label : String) (c : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell c) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (i, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr i}/{bits}")

private def setBaseGas : Int := computeExactGasBudget instr

private def setMissNullCreated : Nat := dictUSetCreated none 8 9 sampleSliceD
private def setHitCreated : Nat := dictUSetCreated (some dictUSet8Root) 8 5 sampleSliceD
private def setHit0Created : Nat := dictUSetCreated (some dictUSet0Root) 0 0 sampleSliceB
private def setWideCreated : Nat := dictUSetCreated (some dictUSet1023Root) 1023 1 sampleSliceE

private def setMissNullGas : Int := setBaseGas + Int.ofNat setMissNullCreated * cellCreateGasPrice
private def setHitGas : Int := setBaseGas + Int.ofNat setHitCreated * cellCreateGasPrice
private def setHit0Gas : Int := setBaseGas + Int.ofNat setHit0Created * cellCreateGasPrice
private def setWideGas : Int := setBaseGas + Int.ofNat setWideCreated * cellCreateGasPrice

private def setMissNullGasMinusOne : Int := if setMissNullGas > 0 then setMissNullGas - 1 else 0
private def setHitGasMinusOne : Int := if setHitGas > 0 then setHitGas - 1 else 0
private def setHit0GasMinusOne : Int := if setHit0Gas > 0 then setHit0Gas - 1 else 0
private def setWideGasMinusOne : Int := if setWideGas > 0 then setWideGas - 1 else 0

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

private def genDICTUSETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/underflow/empty" #[]
    else if shape = 1 then
      mkCase "fuzz/underflow/one" #[.slice sampleSliceA]
    else if shape = 2 then
      mkCase "fuzz/underflow/two" #[.slice sampleSliceA, .int (.num 5)]
    else if shape = 3 then
      mkCase "fuzz/underflow/three" #[.slice sampleSliceA, .int (.num 5), .null]
    else if shape = 4 then
      mkCase "fuzz/n-negative" (mkStack sampleSliceA 5 (.cell dictUSet8Root) (-1))
    else if shape = 5 then
      mkCase "fuzz/n-too-large" (mkStack sampleSliceA 5 (.cell dictUSet8Root) 1024)
    else if shape = 6 then
      mkCase "fuzz/n-nan" #[.slice sampleSliceA, .int (.num 5), .cell dictUSet8Root, .int .nan]
    else if shape = 7 then
      mkCase "fuzz/root-not-cell" (mkStack sampleSliceA 5 (.tuple #[]) 8)
    else if shape = 8 then
      mkCase "fuzz/key-not-int" #[.slice sampleSliceA, .slice sampleSliceA, .cell dictUSet8Root, intV 8]
    else if shape = 9 then
      mkCase "fuzz/value-not-slice" #[(.cell sampleCellA), .int (.num 5), .cell dictUSet8Root, intV 8]
    else if shape = 10 then
      mkCase "fuzz/key-high-nonzero" (mkStack sampleSliceA 256 (.null) 8)
    else if shape = 11 then
      mkCase "fuzz/key-negative" (mkStack sampleSliceA (-1) (.cell dictUSet8Root) 8)
    else if shape = 12 then
      mkCase "fuzz/key-nonzero-at-n0" (mkStack sampleSliceA 1 (.cell dictUSet0Root) 0)
    else if shape = 13 then
      mkCase "fuzz/set-hit" (mkStack sampleSliceD 5 (.cell dictUSet8Root) 8)
    else if shape = 14 then
      mkCase "fuzz/set-miss" (mkStack sampleSliceE 3 (.null) 8)
    else if shape = 15 then
      mkCase "fuzz/set-miss-non-empty" (mkStack sampleSliceE 9 (.cell dictUSet8Root) 8)
    else if shape = 16 then
      mkCase "fuzz/set-zero-hit" (mkStack sampleSliceB 0 (.cell dictUSet0Root) 0)
    else if shape = 17 then
      mkCase "fuzz/set-zero-miss" (mkStack sampleSliceF 0 (.null) 0)
    else if shape = 18 then
      mkCase "fuzz/set-wide-hit" (mkStack sampleSliceE 1 (.cell dictUSet1023Root) 1023)
    else if shape = 19 then
      mkCase "fuzz/set-wide-miss" (mkStack sampleSliceF 2 (.null) 1023)
    else if shape = 20 then
      mkCase "fuzz/malformed-root" (mkStack sampleSliceA 5 (.cell malformedDictCell) 8)
    else if shape = 21 then
      mkCodeCase "fuzz/raw/f412" (mkStack sampleSliceA 5 (.null) 8) raw412
    else if shape = 22 then
      mkCodeCase "fuzz/raw/f413" (mkStack sampleSliceA 5 (.null) 8) raw413
    else if shape = 23 then
      mkCodeCase "fuzz/raw/f414" (mkStack sampleSliceA 5 (.null) 8) raw414
    else if shape = 24 then
      mkCodeCase "fuzz/raw/f415" (mkStack sampleSliceA 5 (.null) 8) raw415
    else if shape = 25 then
      mkCodeCase "fuzz/raw/f416" (mkStack sampleSliceA 5 (.null) 8) raw416
    else if shape = 26 then
      mkCodeCase "fuzz/raw/f417" (mkStack sampleSliceA 5 (.null) 8) raw417
    else if shape = 27 then
      mkCodeCase "fuzz/raw/f411" #[] raw411
    else if shape = 28 then
      mkCodeCase "fuzz/raw/f418" #[] raw418
    else if shape = 29 then
      mkCodeCase "fuzz/raw/truncated" #[] rawF4
    else if shape = 30 then
      mkCase
        "fuzz/gas/miss-exact"
        (mkStack sampleSliceD 9 .null 8)
        (mkGasProgram setMissNullGas)
        (oracleGasLimitsExact setMissNullGas)
    else if shape = 31 then
      mkCase
        "fuzz/gas/miss-minus-one"
        (mkStack sampleSliceD 9 .null 8)
        (mkGasProgram setMissNullGasMinusOne)
        (oracleGasLimitsExactMinusOne setMissNullGasMinusOne)
    else if shape = 32 then
      mkCase
        "fuzz/gas/hit-exact"
        (mkStack sampleSliceD 5 (.cell dictUSet8Root) 8)
        (mkGasProgram setHitGas)
        (oracleGasLimitsExact setHitGas)
    else if shape = 33 then
      mkCase
        "fuzz/gas/hit-minus-one"
        (mkStack sampleSliceD 5 (.cell dictUSet8Root) 8)
        (mkGasProgram setHitGasMinusOne)
        (oracleGasLimitsExactMinusOne setHitGasMinusOne)
    else if shape = 34 then
      mkCase
        "fuzz/gas/zero-hit-exact"
        (mkStack sampleSliceB 0 (.cell dictUSet0Root) 0)
        (mkGasProgram setHit0Gas)
        (oracleGasLimitsExact setHit0Gas)
    else if shape = 35 then
      mkCase
        "fuzz/gas/wide-hit-exact"
        (mkStack sampleSliceE 1 (.cell dictUSet1023Root) 1023)
        (mkGasProgram setWideGas)
        (oracleGasLimitsExact setWideGas)
    else if shape = 36 then
      mkCase
        "fuzz/gas/wide-hit-minus-one"
        (mkStack sampleSliceE 1 (.cell dictUSet1023Root) 1023)
        (mkGasProgram setWideGasMinusOne)
        (oracleGasLimitsExactMinusOne setWideGasMinusOne)
    else if shape = 37 then
      mkCase
        "fuzz/gas/zero-minus"
        (mkStack sampleSliceB 0 (.cell dictUSet0Root) 0)
        (mkGasProgram setHit0GasMinusOne)
        (oracleGasLimitsExactMinusOne setHit0GasMinusOne)
    else if shape = 38 then
      mkCase
        "fuzz/gas/hit-non-empty-miss"
        (mkStack sampleSliceF 9 (.cell dictUSet8Root) 8)
        (mkGasProgram setMissNullGas)
        (oracleGasLimitsExact setMissNullGas)
    else
      mkCodeCase "fuzz/raw/boundary-mix" #[] rawF4
  let case1 : OracleCase := { case0 with name := s!"{case0.name}/{tag}" }
  (case1, rng2)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "dispatch/fallback"
          (runDICTUSETFallback (mkStack sampleSliceA 5 (.cell dictUSet8Root) 8))
          #[.slice sampleSliceA, .int (.num 5), .cell dictUSet8Root, intV 8, intV dispatchSentinel] }
    ,
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDICTUSET #[]) .stkUnd }
    ,
    { name := "unit/runtime/underflow-one" -- [B2]
      run := do
        expectErr "underflow-one" (runDICTUSET #[.slice sampleSliceA]) .stkUnd }
    ,
    { name := "unit/runtime/underflow-two" -- [B2]
      run := do
        expectErr "underflow-two" (runDICTUSET #[.slice sampleSliceA, .int (.num 5)]) .stkUnd }
    ,
    { name := "unit/runtime/underflow-three" -- [B2]
      run := do
        expectErr "underflow-three" (runDICTUSET #[.slice sampleSliceA, .int (.num 5), .null]) .stkUnd }
    ,
    { name := "unit/runtime/n-errors" -- [B3]
      run := do
        expectErr "n-negative" (runDICTUSET (mkStack sampleSliceA 5 (.cell dictUSet8Root) (-1))) .rangeChk
        expectErr "n-too-large" (runDICTUSET (mkStack sampleSliceA 5 (.cell dictUSet8Root) 1024)) .rangeChk
        expectErr "n-nan" (runDICTUSET #[.slice sampleSliceA, .int (.num 5), .cell dictUSet8Root, .int .nan]) .rangeChk }
    ,
    { name := "unit/runtime/type-root" -- [B4]
      run := do
        expectErr "root-not-cell" (runDICTUSET (mkStack sampleSliceA 5 (.tuple #[]) 8)) .typeChk }
    ,
    { name := "unit/runtime/key-type" -- [B5]
      run := do
        expectErr "key-not-int" (runDICTUSET (#[(.slice sampleSliceA), .slice sampleSliceA, .cell dictUSet8Root, intV 8])) .typeChk
        expectErr "key-negative" (runDICTUSET (mkStack sampleSliceA (-1) (.cell dictUSet8Root) 8)) .rangeChk
        expectErr "key-high" (runDICTUSET (mkStack sampleSliceA 256 (.cell dictUSet8Root) 8)) .rangeChk
        expectErr "key-nonzero-n0" (runDICTUSET (mkStack sampleSliceA 1 (.cell dictUSet0Root) 0)) .rangeChk }
    ,
    { name := "unit/runtime/value-type" -- [B6]
      run := do
        expectErr "value-not-slice" (runDICTUSET #[.cell sampleCellA, .int (.num 5), .cell dictUSet8Root, intV 8]) .typeChk }
    ,
    { name := "unit/runtime/semantics-ok-hit-and-miss" -- [B7]
      run := do
        let expectedMiss : Cell := dictUSetExpected! none 8 9 sampleSliceD
        let expectedHit : Cell := dictUSetExpected! (some dictUSet8Root) 8 5 sampleSliceD
        let expectedMissNonEmpty : Cell := dictUSetExpected! (some dictUSet8Root) 8 9 sampleSliceE
        let expectedZero : Cell := dictUSetExpected! (some dictUSet0Root) 0 0 sampleSliceB
        expectOkStack "set-miss-null" (runDICTUSET (mkStack sampleSliceD 9 .null 8)) #[(.cell expectedMiss)]
        expectOkStack "set-hit-root" (runDICTUSET (mkStack sampleSliceD 5 (.cell dictUSet8Root) 8)) #[(.cell expectedHit)]
        expectOkStack "set-miss-non-empty" (runDICTUSET (mkStack sampleSliceE 9 (.cell dictUSet8Root) 8)) #[(.cell expectedMissNonEmpty)]
        expectOkStack "set-zero-hit" (runDICTUSET (mkStack sampleSliceB 0 (.cell dictUSet0Root) 0)) #[(.cell expectedZero)] }
    ,
    { name := "unit/runtime/malformed-root" -- [B8]
      run := do
        expectErr "malformed-root" (runDICTUSET (mkStack sampleSliceA 5 (.cell malformedDictCell) 8)) .dictErr }
    ,
    { name := "unit/asm/encode/decode" -- [B9]
      run := do
        expectAssembleEq "asm/encode" raw416 instr
        expectAssembleInv "asm/inv/non-int-unsigned" (.dictSet false true false .set)
        let _ ← expectDecodeStep "decode/416" (opcodeSlice16 0xF416) instr
        let _ ← expectDecodeStep "decode/412" (opcodeSlice16 0xF412) (.dictSet false false false .set)
        let _ ← expectDecodeStep "decode/415" (opcodeSlice16 0xF415) (.dictSet true false true .set)
        let _ ← expectDecodeStep "decode/417" (opcodeSlice16 0xF417) (.dictSet true true true .set)
        expectDecodeInv "decode/f411" raw411
        expectDecodeInv "decode/f418" raw418
        expectDecodeInv "decode/truncated" rawF4 }
  ]
  oracle := #[
    mkCase "oracle/underflow-empty" #[] -- [B2]
    ,
    mkCase "oracle/underflow-one" #[.slice sampleSliceA] -- [B2]
    ,
    mkCase "oracle/underflow-two" #[.slice sampleSliceA, .int (.num 5)] -- [B2]
    ,
    mkCase "oracle/underflow-three" #[.slice sampleSliceA, .int (.num 5), .null] -- [B2]
    ,
    mkCase "oracle/n-negative" (mkStack sampleSliceA 5 (.cell dictUSet8Root) (-1)) -- [B3]
    ,
    mkCase "oracle/n-too-large" (mkStack sampleSliceA 5 (.cell dictUSet8Root) 1024) -- [B3]
    ,
    mkCase "oracle/n-nan" #[.slice sampleSliceA, .int (.num 5), .cell dictUSet8Root, .int .nan] -- [B3]
    ,
    mkCase "oracle/type-root" (mkStack sampleSliceA 5 (.tuple #[]) 8) -- [B4]
    ,
    mkCase "oracle/key-not-int" (#[.slice sampleSliceA, .slice sampleSliceA, .cell dictUSet8Root, intV 8]) -- [B5]
    ,
    mkCase "oracle/value-not-slice" (#[(.cell sampleCellA), .int (.num 5), .cell dictUSet8Root, intV 8]) -- [B6]
    ,
    mkCase "oracle/key-high" (mkStack sampleSliceA 256 (.cell dictUSet8Root) 8) -- [B5]
    ,
    mkCase "oracle/key-low" (mkStack sampleSliceA (-1) (.cell dictUSet8Root) 8) -- [B5]
    ,
    mkCase "oracle/key-nonzero-n0" (mkStack sampleSliceA 1 (.cell dictUSet0Root) 0) -- [B5]
    ,
    mkCase "oracle/set-miss-null" (mkStack sampleSliceD 9 .null 8) -- [B7]
    ,
    mkCase "oracle/set-miss-non-empty" (mkStack sampleSliceE 3 (.cell dictUSet8Root) 8) -- [B7]
    ,
    mkCase "oracle/set-hit" (mkStack sampleSliceD 5 (.cell dictUSet8Root) 8) -- [B7]
    ,
    mkCase "oracle/set-zero-hit" (mkStack sampleSliceB 0 (.cell dictUSet0Root) 0) -- [B5][B7]
    ,
    mkCase "oracle/set-wide-hit" (mkStack sampleSliceE 1 (.cell dictUSet1023Root) 1023) -- [B5][B7]
    ,
    mkCase "oracle/set-wide-miss" (mkStack sampleSliceF 2 (.null) 1023) -- [B5][B7]
    ,
    mkCase "oracle/malformed-root" (mkStack sampleSliceA 5 (.cell malformedDictCell) 8) -- [B8]
    ,
    mkCase "oracle/asm/encode" #[] (#[instr]) -- [B9]
    ,
    mkCase "oracle/asm/inv" #[] (#[.dictSet false true false .set]) -- [B9]
    ,
    mkCodeCase "oracle/decode/412" #[] raw412 -- [B9]
    ,
    mkCodeCase "oracle/decode/413" #[] raw413 -- [B9]
    ,
    mkCodeCase "oracle/decode/414" #[] raw414 -- [B9]
    ,
    mkCodeCase "oracle/decode/415" #[] raw415 -- [B9]
    ,
    mkCodeCase "oracle/decode/416" #[] raw416 -- [B9]
    ,
    mkCodeCase "oracle/decode/417" #[] raw417 -- [B9]
    ,
    mkCodeCase "oracle/decode/411-invalid" #[] raw411 -- [B9]
    ,
    mkCodeCase "oracle/decode/418-invalid" #[] raw418 -- [B9]
    ,
    mkCodeCase "oracle/decode/truncated" #[] rawF4 -- [B9]
    ,
    mkCase "oracle/gas/hit-exact" (mkStack sampleSliceD 5 (.cell dictUSet8Root) 8) (mkGasProgram setHitGas) (oracleGasLimitsExact setHitGas) -- [B10]
    ,
    mkCase "oracle/gas/hit-minus-one" (mkStack sampleSliceD 5 (.cell dictUSet8Root) 8) (mkGasProgram setHitGasMinusOne) (oracleGasLimitsExactMinusOne setHitGasMinusOne) -- [B10]
    ,
    mkCase "oracle/gas/miss-exact" (mkStack sampleSliceD 9 .null 8) (mkGasProgram setMissNullGas) (oracleGasLimitsExact setMissNullGas) -- [B10]
    ,
    mkCase "oracle/gas/miss-minus-one" (mkStack sampleSliceD 9 .null 8) (mkGasProgram setMissNullGasMinusOne) (oracleGasLimitsExactMinusOne setMissNullGasMinusOne) -- [B10]
    ,
    mkCase "oracle/gas/zero-exact" (mkStack sampleSliceB 0 (.cell dictUSet0Root) 0) (mkGasProgram setHit0Gas) (oracleGasLimitsExact setHit0Gas) -- [B10]
    ,
    mkCase "oracle/gas/zero-minus" (mkStack sampleSliceB 0 (.cell dictUSet0Root) 0) (mkGasProgram setHit0GasMinusOne) (oracleGasLimitsExactMinusOne setHit0GasMinusOne) -- [B10]
    ,
    mkCase "oracle/gas/wide-exact" (mkStack sampleSliceE 1 (.cell dictUSet1023Root) 1023) (mkGasProgram setWideGas) (oracleGasLimitsExact setWideGas) -- [B10]
    ,
    mkCase "oracle/gas/wide-minus" (mkStack sampleSliceE 1 (.cell dictUSet1023Root) 1023) (mkGasProgram setWideGasMinusOne) (oracleGasLimitsExactMinusOne setWideGasMinusOne) -- [B10]
  ]
  fuzz := #[
    {
      seed := fuzzSeed
      count := 500
      gen := genDICTUSETFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUSET
