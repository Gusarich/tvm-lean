import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREPLACEREF

/-!
INSTRUCTION: DICTUREPLACEREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictDictSet` handles `.dictSet` instructions and ignores all others by delegating to `next`.

2. [B2] Stack arity and ordering branch.
   - `checkUnderflow 4` is required.
   - Stack shape is `valueRef`, `key`, `dict`, `n` (top item is popped first).
   - Underflow in 0..3 item stacks must raise `.stkUnd`.

3. [B3] Width (`n`) validation branch.
   - `popNatUpTo 1023` accepts `0..1023`.
   - Negative, `.nan`, or too-large (`>1023`) widths raise `.rangeChk`.

4. [B4] Unsigned key materialization branch.
   - `intKey=true, unsigned=true` uses `dictKeyBits?`.
   - `n=0` only accepts key `0`.
   - For `n=1`, only `0` and `1` are valid.
   - Larger widths enforce range and also reject negative values.
   - Width mismatch between stack `n` and dictionary key length can produce a non-hit (old root returned, `0`).

5. [B5] By-ref value branch.
   - `.dictSet ... byRef=true` requires a `.cell` value.
   - Non-cell value raises `.typeChk`.

6. [B6] Replace semantics branch.
   - Hit path: dictionary is rebuilt as needed and `-1` is pushed.
   - Miss path: dictionary unchanged (or `null`) and `0` is pushed.
   - `null` miss and non-null miss are both valid.

7. [B7] Type and structural-error branch.
   - Non-int key for int-key mode raises `.typeChk`.
   - Non-cell dictionary raises `.typeChk`.
   - Malformed existing dictionary may raise `.dictErr`.

8. [B8] Assembler branch.
   - `.dictSet true true true .replace` encodes to `0xF427`.
   - `.dictSet false true true .replace` is invalid (`.invOpcode`).
   - Adjacent opcodes map to expected `dictSet` variants or `.invOpcode` via decoder bounds.

9. [B9] Decoder boundary branch.
   - `0xF427` decodes to `DICTUREPLACEREF`.
   - `0xF426`/`0xF428` are boundary cases for neighboring ranges.
   - Truncated `0xF4` (8-bit) is invalid.

10. [B10] Gas accounting branch.
    - Base cost is `computeExactGasBudget instr`.
    - Hit replacement adds `created * cellCreateGasPrice` where `created` comes from `dictSetRefWithCells`.
    - Miss path has no created-cell surcharge.
    - `exact` budgets must pass and `exact-1` budgets must fail (per path).

11. [B11] Width boundaries.
    - `n=0` and `n=1023` are allowed by the runtime width check; conversion and key constraints still apply.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branches it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTUREPLACEREF" }

private def instr : Instr :=
  .dictSet true true true .replace

private def dispatchSentinel : Int := 13021

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA1 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB2 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def valueD : Cell :=
  Cell.mkOrdinary (natToBits 0xD4 8) #[]

private def badSliceValue : Slice :=
  mkSliceFromBits (natToBits 0xEE 8)

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def requireBits (label : String) (k : Int) (n : Nat) : BitString :=
  match dictKeyBits? k n true with
  | some bits => bits
  | none => panic! s!"{label}: invalid unsigned key={k} for n={n}"

private def mkDictRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits := requireBits label k n
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while setting key={k}"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed for key={k}: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: dictionary construction yielded no root"

private def replaceUnsignedCreated (label : String) (root : Cell) (n : Nat) (key : Int) (value : Cell) : Nat :=
  match dictSetRefWithCells (some root) (requireBits label key n) value .replace with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error _ => 0

private def replaceUnsignedRoot! (label : String) (root : Cell) (n : Nat) (key : Int) (value : Cell) : Cell :=
  match dictSetRefWithCells (some root) (requireBits label key n) value .replace with
  | .ok (some r, _ok, _created, _loaded) => r
  | .ok (none, _ok, _created, _loaded) =>
      panic! s!"{label}: unexpected miss on replace key={key} n={n}"
  | .error e =>
      panic! s!"{label}: replace failed: {reprStr e}"

private def dict8Single0 : Cell :=
  mkDictRefRoot! "dict8/single/0" 8 #[(0, valueA)]

private def dict8Single255 : Cell :=
  mkDictRefRoot! "dict8/single/255" 8 #[(255, valueA)]

private def dict8Pair : Cell :=
  mkDictRefRoot! "dict8/pair" 8 #[(0, valueA), (255, valueB)]

private def dict8Fork : Cell :=
  mkDictRefRoot! "dict8/fork" 8 #[(4, valueA), (5, valueB)]

private def dict8Shared : Cell :=
  mkDictRefRoot! "dict8/shared" 8 #[(120, valueA), (121, valueB)]

private def dict0Single : Cell :=
  mkDictRefRoot! "dict/0/single" 0 #[(0, valueA)]

private def dict1023Single : Cell :=
  mkDictRefRoot! "dict/1023/single" 1023 #[(0, valueA)]

private def expectedHit8Single : Cell :=
  replaceUnsignedRoot! "expected-hit-8-single" dict8Single0 8 0 valueB

private def expectedHit8Pair : Cell :=
  replaceUnsignedRoot! "expected-hit-8-pair" dict8Pair 8 0 valueC

private def expectedHit8Single255 : Cell :=
  replaceUnsignedRoot! "expected-hit-8-255" dict8Single255 8 255 valueD

private def expectedHit0Single : Cell :=
  replaceUnsignedRoot! "expected-hit-0-single" dict0Single 0 0 valueA

private def expectedHit1023Single : Cell :=
  replaceUnsignedRoot! "expected-hit-1023" dict1023Single 1023 0 valueB

private def hitSingle8Created : Nat :=
  replaceUnsignedCreated "hit-created-8-single" dict8Single0 8 0 valueB

private def hitPair8Created : Nat :=
  replaceUnsignedCreated "hit-created-8-pair" dict8Pair 8 0 valueC

private def hit2558Created : Nat :=
  replaceUnsignedCreated "hit-created-8-255" dict8Single255 8 255 valueD

private def hit1023Created : Nat :=
  replaceUnsignedCreated "hit-created-1023" dict1023Single 1023 0 valueB

private def minusOneOrZero (g : Int) : Int :=
  if g > 0 then g - 1 else 0

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := minusOneOrZero baseGas

private def missGas : Int := baseGas
private def missGasMinusOne : Int := minusOneOrZero missGas

private def hit8SingleGas : Int :=
  baseGas + (Int.ofNat hitSingle8Created * cellCreateGasPrice)
private def hit8SingleGasMinusOne : Int := minusOneOrZero hit8SingleGas

private def hit8PairGas : Int :=
  baseGas + (Int.ofNat hitPair8Created * cellCreateGasPrice)
private def hit8PairGasMinusOne : Int := minusOneOrZero hit8PairGas

private def hit1023Gas : Int :=
  baseGas + (Int.ofNat hit1023Created * cellCreateGasPrice)
private def hit1023GasMinusOne : Int := minusOneOrZero hit1023Gas

private def rawF422 : Cell := Cell.mkOrdinary (natToBits 0xF422 16) #[]
private def rawF423 : Cell := Cell.mkOrdinary (natToBits 0xF423 16) #[]
private def rawF424 : Cell := Cell.mkOrdinary (natToBits 0xF424 16) #[]
private def rawF425 : Cell := Cell.mkOrdinary (natToBits 0xF425 16) #[]
private def rawF426 : Cell := Cell.mkOrdinary (natToBits 0xF426 16) #[]
private def rawF427 : Cell := Cell.mkOrdinary (natToBits 0xF427 16) #[]
private def rawF428 : Cell := Cell.mkOrdinary (natToBits 0xF428 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

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
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDICTUREPLACEREFDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def runDICTUREPLACEREFDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def expectDecodeInv (label : String) (cell : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (i, bits, _) => throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr i} with {bits} bits")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected .invOpcode, got success")

private def mkGasProgram (gas : Int) (i : Instr) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, i]

private def genDICTUREPLACEREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 36
  let (randBool0, rng2) := randBool rng1
  let (randBool1, rng3) := randBool rng2
  let (case0, rng4) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[], rng3)
    else if shape = 1 then
      (mkCase "fuzz/underflow/one" #[.cell valueA], rng3)
    else if shape = 2 then
      (mkCase "fuzz/underflow/two" #[.cell valueA, .int (.num 8)], rng3)
    else if shape = 3 then
      (mkCase "fuzz/underflow/three" #[.cell valueA, .int (.num 8), .cell dict8Single0], rng3)
    else if shape = 4 then
      (mkCase "fuzz/ok/miss-null-8" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 9)]), rng3)
    else if shape = 5 then
      (mkCase "fuzz/ok/miss-null-1023" (#[.cell valueA, .int (.num 0), .null, .int (.num 1023)]), rng3)
    else if shape = 6 then
      (mkCase "fuzz/ok/miss-nonnull-width-mismatch" (#[.cell valueA, .int (.num 4), .cell dict8Single0, .int (.num 4)]), rng3)
    else if shape = 7 then
      (mkCase "fuzz/ok/miss-nonnull-255" (#[.cell valueD, .int (.num 255), .cell dict8Single0, .int (.num 8)]), rng3)
    else if shape = 8 then
      (mkCase "fuzz/ok/hit-single" (#[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)]), rng3)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit-pair" (#[.cell valueD, .int (.num 0), .cell dict8Pair, .int (.num 8)]), rng3)
    else if shape = 10 then
      (mkCase "fuzz/ok/hit-zero-width" (#[.cell valueC, .int (.num 0), .cell dict0Single, .int (.num 0)]), rng3)
    else if shape = 11 then
      (mkCase "fuzz/ok/hit-1023" (#[.cell valueC, .int (.num 0), .cell dict1023Single, .int (.num 1023)]), rng3)
    else if shape = 12 then
      (mkCase "fuzz/err/key-neg" (#[.cell valueA, .int (.num (-1)), .cell dict8Single0, .int (.num 8)]), rng3)
    else if shape = 13 then
      (mkCase "fuzz/err/key-high" (#[.cell valueA, .int (.num 256), .cell dict8Single0, .int (.num 8)]), rng3)
    else if shape = 14 then
      (mkCase "fuzz/err/key-oob-zero-width" (#[.cell valueA, .int (.num 1), .cell dict0Single, .int (.num 0)]), rng3)
    else if shape = 15 then
      (mkCase "fuzz/err/n-negative" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num (-1))]), rng3)
    else if shape = 16 then
      (mkCase "fuzz/err/n-nan" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int .nan]), rng3)
    else if shape = 17 then
      (mkCase "fuzz/err/n-overflow" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 1024)]), rng3)
    else if shape = 18 then
      (mkCase "fuzz/err/type-key" (#[.cell valueA, .int (.num 0), .cell dict8Single0, .slice badSliceValue]), rng3)
    else if shape = 19 then
      (mkCase "fuzz/err/type-value" (#[.int (.num 0), .int (.num 0), .cell dict8Single0, .int (.num 8)]), rng3)
    else if shape = 20 then
      (mkCase "fuzz/err/type-dict" (#[.cell valueA, .int (.num 0), .tuple #[], .int (.num 8)]), rng3)
    else if shape = 21 then
      (mkCase "fuzz/err/malformed-root" (#[.cell valueA, .int (.num 0), .cell malformedDict, .int (.num 8)]), rng3)
    else if shape = 22 then
      (mkCodeCase "fuzz/decode/f425" (#[.cell valueA, .int (.num 255), .cell dict8Single255, .int (.num 8)]) rawF425, rng3)
    else if shape = 23 then
      (mkCodeCase "fuzz/decode/f426" (#[.cell valueA, .int (.num 255), .cell dict8Single255, .int (.num 8)]) rawF426, rng3)
    else if shape = 24 then
      (mkCodeCase "fuzz/decode/f427" (#[.cell valueA, .int (.num 255), .cell dict8Single255, .int (.num 8)]) rawF427, rng3)
    else if shape = 25 then
      (mkCodeCase "fuzz/decode/f428" (#[.cell valueA, .int (.num 255), .cell dict8Single255, .int (.num 8)]) rawF428, rng3)
    else if shape = 26 then
      (mkCodeCase "fuzz/decode/truncated" (#[.cell valueA, .int (.num 255), .cell dict8Single255, .int (.num 8)]) rawF4, rng3)
    else if shape = 27 then
      if randBool0 then
        (mkCase "fuzz/gas/miss-exact" (#[.cell valueA, .int (.num 8), .null, .int (.num 8)] )
          (mkGasProgram missGas instr) (oracleGasLimitsExact missGas), rng3)
      else
        (mkCase "fuzz/gas/miss-1023-exact" (#[.cell valueA, .int (.num 0), .null, .int (.num 1023)] )
          (mkGasProgram missGas instr) (oracleGasLimitsExact missGas), rng3)
    else if shape = 28 then
      (mkCase "fuzz/gas/miss-minus-one" (#[.cell valueA, .int (.num 8), .null, .int (.num 8)] )
        (mkGasProgram missGasMinusOne instr) (oracleGasLimitsExactMinusOne missGasMinusOne), rng3)
    else if shape = 29 then
      if randBool1 then
        (mkCase "fuzz/gas/hit-single-exact" (#[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)] )
          (mkGasProgram hit8SingleGas instr) (oracleGasLimitsExact hit8SingleGas), rng3)
      else
        (mkCase "fuzz/gas/hit-1023-exact" (#[.cell valueB, .int (.num 0), .cell dict1023Single, .int (.num 1023)] )
          (mkGasProgram hit1023Gas instr) (oracleGasLimitsExact hit1023Gas), rng3)
    else if shape = 30 then
      (mkCase "fuzz/gas/hit-single-minus-one" (#[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)] )
        (mkGasProgram hit8SingleGasMinusOne instr) (oracleGasLimitsExactMinusOne hit8SingleGasMinusOne), rng3)
    else if shape = 31 then
      if randBool0 then
        (mkCase "fuzz/gas/hit-pair-exact" (#[.cell valueC, .int (.num 0), .cell dict8Pair, .int (.num 8)] )
          (mkGasProgram hit8PairGas instr) (oracleGasLimitsExact hit8PairGas), rng3)
      else
        (mkCase "fuzz/gas/hit-255-exact" (#[.cell valueD, .int (.num 255), .cell dict8Single255, .int (.num 8)] )
          (mkGasProgram baseGas instr) (oracleGasLimitsExact baseGas), rng3)
    else if shape = 32 then
      (mkCase "fuzz/gas/hit-pair-minus-one" (#[.cell valueC, .int (.num 0), .cell dict8Pair, .int (.num 8)] )
        (mkGasProgram hit8PairGasMinusOne instr) (oracleGasLimitsExactMinusOne hit8PairGasMinusOne), rng3)
    else if shape = 33 then
      (mkCodeCase "fuzz/decode/f422" (#[.cell valueA, .int (.num 0), .null, .int (.num 8)]) rawF422, rng3)
    else if shape = 34 then
      (mkCodeCase "fuzz/decode/f423" (#[.cell valueA, .int (.num 0), .null, .int (.num 8)]) rawF423, rng3)
    else if shape = 35 then
      (mkCodeCase "fuzz/ok/decode/raw" (#[.cell valueA, .int (.num 0), .cell dict8Single0, .int (.num 8)]) rawF427, rng3)
    else
      (mkCase "fuzz/default" (#[.cell valueA, .int (.num 0), .cell dict8Single0, .int (.num 8)]), rng3)
  let (tag, rng5) := randNat rng4 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st ←
          match runDICTUREPLACEREFDispatchFallback (#[.cell valueA, .int (.num 0), .cell dict8Single0, .int (.num 8)]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"fallback failed: {e}")
        if st == #[.cell valueA, .int (.num 0), .cell dict8Single0, .int (.num 8), intV dispatchSentinel] then
          pure ()
        else
          throw (IO.userError s!"fallback failed: expected sentinel pass-through") }
    , { name := "unit/asm/encode" -- [B8]
        run := do
          match assembleCp0 [instr] with
          | .ok c =>
              if c.bits = natToBits 0xF427 16 then
                pure ()
              else
                throw (IO.userError s!"unit/asm/encode: wrong bits {reprStr c.bits}")
          | .error e =>
              throw (IO.userError s!"unit/asm/encode: {e}") }
    , { name := "unit/asm/invalid-unsigned-non-int" -- [B8]
        run := do
          expectAssembleInvOpcode "unit/asm/invalid-unsigned-non-int" (.dictSet false true true .replace) }
    , { name := "unit/decode/valid" -- [B9]
        run := do
          let s := Slice.ofCell rawF427
          let _ ← expectDecodeStep "decode/0xF427" s (.dictSet true true true .replace) 16
          pure () }
    , { name := "unit/decode/boundaries" -- [B9]
        run := do
          let s0 : Slice := Slice.ofCell rawF426
          let _ ← expectDecodeStep "decode/f426" s0 (.dictSet true true false .replace) 16
          let s1 : Slice := Slice.ofCell rawF428
          let _ ← expectDecodeStep "decode/f428" s1 (.dictSet true false false .replace) 16
          expectDecodeInv "decode/truncated" rawF4 }
    , { name := "unit/runtime/ok-hit" -- [B6]
        run := do
          expectOkStack
            "runtime/ok-hit"
            (runDICTUREPLACEREFDirect (#[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)]))
            #[.cell expectedHit8Single, intV (-1)] }
    , { name := "unit/runtime/ok-hit-255" -- [B6]
        run := do
          expectOkStack
            "runtime/ok-hit-255"
            (runDICTUREPLACEREFDirect (#[.cell valueD, .int (.num 255), .cell dict8Single255, .int (.num 8)]))
            #[.cell expectedHit8Single255, intV (-1)] }
    , { name := "unit/runtime/ok-hit-1023" -- [B4] [B11]
        run := do
          expectOkStack
            "runtime/ok-hit-1023"
            (runDICTUREPLACEREFDirect (#[.cell valueC, .int (.num 0), .cell dict1023Single, .int (.num 1023)]))
            #[.cell expectedHit1023Single, intV (-1)] }
    , { name := "unit/runtime/ok-miss-null" -- [B6]
        run := do
          expectOkStack
            "runtime/ok-miss-null"
            (runDICTUREPLACEREFDirect (#[.cell valueA, .int (.num 9), .null, .int (.num 8)]))
            #[.null, intV 0] }
    , { name := "unit/runtime/ok-miss-nonnull" -- [B6]
        run := do
          expectOkStack
            "runtime/ok-miss-nonnull"
            (runDICTUREPLACEREFDirect (#[.cell valueB, .int (.num 1), .cell dict8Single0, .int (.num 8)]))
            #[.cell dict8Single0, intV 0] }
    , { name := "unit/runtime/ok/miss-width-mismatch" -- [B4]
        run := do
          expectOkStack
            "runtime/miss-width-mismatch"
            (runDICTUREPLACEREFDirect (#[.cell valueB, .int (.num 9), .cell dict8Single0, .int (.num 4)]))
            #[.cell dict8Single0, intV 0] }
    , { name := "unit/runtime/ok/zero-width-hit" -- [B11]
        run := do
          expectOkStack
            "runtime/zero-width-hit"
            (runDICTUREPLACEREFDirect (#[.cell valueA, .int (.num 0), .cell dict0Single, .int (.num 0)]))
            #[.cell expectedHit0Single, intV (-1)] }
    , { name := "unit/runtime/underflow/empty" -- [B2]
        run := do
          expectErr "runtime/underflow-empty" (runDICTUREPLACEREFDirect #[]) .stkUnd }
    , { name := "unit/runtime/underflow/one" -- [B2]
        run := do
          expectErr "runtime/underflow-one" (runDICTUREPLACEREFDirect #[.cell valueA]) .stkUnd }
    , { name := "unit/runtime/underflow/two" -- [B2]
        run := do
          expectErr "runtime/underflow-two" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num 0)]) .stkUnd }
    , { name := "unit/runtime/underflow/three" -- [B2]
        run := do
          expectErr "runtime/underflow-three" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num 0), .cell dict8Single0]) .stkUnd }
    , { name := "unit/runtime/errors" -- [B3] [B4] [B5] [B7]
        run := do
          expectErr "err/n-negative" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num (-1)), .cell dict8Single0, .int (.num 8)]) .rangeChk
          expectErr "err/n-nan" (runDICTUREPLACEREFDirect #[.cell valueA, .int .nan, .cell dict8Single0, .int (.num 8)]) .rangeChk
          expectErr "err/n-too-large" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num 1024), .cell dict8Single0, .int (.num 8)]) .rangeChk
          expectErr "err/key-high" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num 256), .cell dict8Single0, .int (.num 8)]) .rangeChk
          expectErr "err/key-neg" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num (-1)), .cell dict8Single0, .int (.num 8)]) .rangeChk
          expectErr "err/key-zero-width-nonzero" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num 1), .cell dict0Single, .int (.num 0)]) .rangeChk
          expectErr "err/key-type" (runDICTUREPLACEREFDirect #[.cell valueA, .slice badSliceValue, .cell dict8Single0, .int (.num 8)]) .typeChk
          expectErr "err/value-type" (runDICTUREPLACEREFDirect #[.slice badSliceValue, .int (.num 0), .cell dict8Single0, .int (.num 8)]) .typeChk
          expectErr "err/dict-type" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num 0), .tuple #[], .int (.num 8)]) .typeChk
          expectErr "err/malformed" (runDICTUREPLACEREFDirect #[.cell valueA, .int (.num 0), .cell malformedDict, .int (.num 8)]) .dictErr }
    , { name := "unit/gas-check" -- [B10]
        run := do
          if baseGas > 0 then
            pure ()
          else
            throw (IO.userError "baseGas must be > 0") }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/dispatch/fallback" (#[])
      (#[]) ,
    -- [B2]
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one" #[.cell valueA],
    mkCase "oracle/underflow/two" #[.cell valueA, .int (.num 8)],
    mkCase "oracle/underflow/three" #[.cell valueA, .int (.num 8), .cell dict8Single0],
    -- [B3]
    mkCase "oracle/err/n-negative" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num (-1))]),
    mkCase "oracle/err/n-nan" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int .nan]),
    mkCase "oracle/err/n-overflow" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 1024)]),
    -- [B4]
    mkCase "oracle/err/key-high" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 256)]),
    mkCase "oracle/err/key-neg" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num (-1))]),
    mkCase "oracle/err/key-zero-width-nonzero" (#[.cell valueA, .int (.num 0), .cell dict0Single, .int (.num 1)]),
    mkCase "oracle/miss/width-mismatch" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 4)]),
    -- [B5]
    mkCase "oracle/ok/hit" (#[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)]),
    mkCase "oracle/ok/miss-null" (#[.cell valueA, .int (.num 8), .null, .int (.num 8)]),
    mkCase "oracle/ok/hit-zero-width" (#[.cell valueA, .int (.num 0), .cell dict0Single, .int (.num 0)]),
    mkCase "oracle/ok/hit-255" (#[.cell valueD, .int (.num 255), .cell dict8Single255, .int (.num 8)]),
    mkCase "oracle/ok/miss-nonnull" (#[.cell valueA, .int (.num 1), .cell dict8Single0, .int (.num 8)]),
    mkCase "oracle/ok/hit-pair" (#[.cell valueC, .int (.num 0), .cell dict8Pair, .int (.num 8)]),
    mkCase "oracle/ok/hit-1023" (#[.cell valueB, .int (.num 0), .cell dict1023Single, .int (.num 1023)]),
    mkCase "oracle/hit-program-stack-extra" (#[.int (.num 777), .cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)]),
    -- [B7]
    mkCase "oracle/err/type-key" (#[.cell valueA, .slice badSliceValue, .cell dict8Single0, .int (.num 8)]),
    mkCase "oracle/err/type-value" (#[.slice badSliceValue, .int (.num 0), .cell dict8Single0, .int (.num 8)]),
    mkCase "oracle/err/dict-type" (#[.cell valueA, .int (.num 0), .tuple #[], .int (.num 8)]),
    mkCase "oracle/err/malformed" (#[.cell valueA, .int (.num 0), .cell malformedDict, .int (.num 8)]),
    -- [B8]
    mkCodeCase "oracle/code/invalid-non-int-unsigned" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF425,
    mkCodeCase "oracle/code/valid-f426" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF426,
    mkCodeCase "oracle/code/valid-f427" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF427,
    mkCodeCase "oracle/code/inv-422" (#[.cell valueA, .int (.num 8), .null, .int (.num 8)]) rawF422,
    mkCodeCase "oracle/code/truncated" (#[] : Array Value) rawF4,
    -- [B9]
    mkCodeCase "oracle/code/boundary-428" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF428,
    mkCodeCase "oracle/code/valid-f425" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF425,
    mkCodeCase "oracle/code/valid-f424" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF424,
    mkCodeCase "oracle/code/valid-f423" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF423,
    -- [B10]
    mkCase "oracle/gas/miss-exact" (#[.cell valueA, .int (.num 8), .null, .int (.num 8)] )
      (mkGasProgram missGas instr)
      (oracleGasLimitsExact missGas),
    mkCase "oracle/gas/miss-minus-one" (#[.cell valueA, .int (.num 8), .null, .int (.num 8)] )
      (mkGasProgram missGasMinusOne instr)
      (oracleGasLimitsExactMinusOne missGasMinusOne),
    mkCase "oracle/gas/hit-8single" (#[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)] )
      (mkGasProgram hit8SingleGas instr)
      (oracleGasLimitsExact hit8SingleGas),
    mkCase "oracle/gas/hit-8single-minus-one" (#[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)] )
      (mkGasProgram hit8SingleGasMinusOne instr)
      (oracleGasLimitsExactMinusOne hit8SingleGasMinusOne),
    mkCase "oracle/gas/hit-pair" (#[.cell valueC, .int (.num 0), .cell dict8Pair, .int (.num 8)] )
      (mkGasProgram hit8PairGas instr)
      (oracleGasLimitsExact hit8PairGas),
    mkCase "oracle/gas/hit-pair-minus-one" (#[.cell valueC, .int (.num 0), .cell dict8Pair, .int (.num 8)] )
      (mkGasProgram hit8PairGasMinusOne instr)
      (oracleGasLimitsExactMinusOne hit8PairGasMinusOne),
    mkCase "oracle/gas/hit-1023" (#[.cell valueB, .int (.num 0), .cell dict1023Single, .int (.num 1023)] )
      (mkGasProgram hit1023Gas instr)
      (oracleGasLimitsExact hit1023Gas),
    mkCase "oracle/gas/base" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)] )
      (mkGasProgram baseGas instr)
      (oracleGasLimitsExact baseGas),
    mkCase "oracle/gas/base-minus-one" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)] )
      (mkGasProgram baseGasMinusOne instr)
      (oracleGasLimitsExactMinusOne baseGasMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTUREPLACEREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREPLACEREF
