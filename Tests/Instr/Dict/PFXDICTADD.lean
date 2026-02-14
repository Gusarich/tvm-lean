import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PFXDICTADD

/-!
INSTRUCTION: PFXDICTADD

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch:
   - `execInstrDictExt` handles `.dictExt (.pfxSet .add)` and forwards unsupported instructions via `next`.

2. [B2] Stack arity:
   - `checkUnderflow 4` enforces the 4-stack-operand layout
     (`newValue`, `key`, `dict`, `n`).

3. [B3] Width parsing and range checks:
   - `popNatUpTo 1023` enforces `n` as a finite integer in `[0,1023]`.
   - `n` as `nan`, negative, or out-of-range yields `.rangeChk`.

4. [B4] Type checks:
   - `newValue` must be a `.slice`.
   - `key` must be `.slice` for this opcode variant.
   - `dict` must be `.null` or `.cell`, otherwise `.typeChk`.

5. [B5] Runtime key availability:
   - For slice-key mode, `key` must have at least `n` bits, otherwise `.cellUnd`.

6. [B6] Slice truncation boundary / no-op case:
   - Key-slice reads exactly `n` bits; excess bits are ignored.
   - In practical terms this can produce the same behavior as `.add` no-op paths for mismatched
     truncated prefixes (e.g. short `n` with longer supplied slice).

7. [B7] Dictionary add semantics:
   - Empty/malformed or non-existent matches produce insertion with `-1` and a rewritten root.
   - Exact key hit keeps root unchanged and pushes `0`.

8. [B8] Malformed dictionary handling:
   - Invalid prefix-dictionary cells propagate `.dictErr`.

9. [B9] Assembler constraints:
   - No `.dictExt` encoder path exists for pfx instructions.
   - `.dictSet ...` variants should encode to `.invOpcode`.

10. [B10] Decoder behavior:
    - `0xF472` decodes to `.dictExt (.pfxSet .add)`.
    - `0xF470`, `0xF471`, `0xF473` decode to sibling prefix-dict opcodes.
    - `0xF46C` and truncated `0xF4` are invalid.

11. [B11] Gas accounting:
    - Base is `computeExactGasBudget`.
    - Additional gas proportional to `created * cellCreateGasPrice`.
    - Exact and exact-minus-one gas budgets are both exercised.

TOTAL BRANCHES: 11
-/

private def pfxDictAddId : InstrId :=
  { name := "PFXDICTADD" }

private def instrAdd : Instr :=
  .dictExt (.pfxSet .add)

private def raw470 : Cell :=
  Cell.mkOrdinary (natToBits 0xF470 16) #[]
private def raw471 : Cell :=
  Cell.mkOrdinary (natToBits 0xF471 16) #[]
private def raw472 : Cell :=
  Cell.mkOrdinary (natToBits 0xF472 16) #[]
private def raw473 : Cell :=
  Cell.mkOrdinary (natToBits 0xF473 16) #[]
private def raw46C : Cell :=
  Cell.mkOrdinary (natToBits 0xF46C 16) #[]
private def rawF4 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def sampleSliceA : Slice :=
  mkSliceFromBits (natToBits 0xAA 8)
private def sampleSliceB : Slice :=
  mkSliceFromBits (natToBits 0xBB 8)
private def sampleSliceC : Slice :=
  mkSliceFromBits (natToBits 0xCC 8)
private def sampleSliceD : Slice :=
  mkSliceFromBits (natToBits 0xDD 8)
private def sampleSliceE : Slice :=
  mkSliceFromBits (natToBits 0xEE 8)

private def sampleCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x11 8) #[]
private def sampleCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x22 8) #[]
private def sampleCellC : Cell :=
  Cell.mkOrdinary (natToBits 0x33 8) #[]
private def sampleCellD : Cell :=
  Cell.mkOrdinary (natToBits 0x44 8) #[]

private def malformedCell : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkSliceKey (n : Nat) (value : Nat) : Slice :=
  mkSliceFromBits (natToBits value n)

private def requireBits (label : String) (key : Int) (n : Nat) : BitString :=
  match dictKeyBits? key n true with
  | some bits => bits
  | none => panic! s!"{label}: invalid key key={key} for n={n}"

private def mkSliceDictRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for e in entries do
      let (k, v) := e
      let bits := requireBits label k n
      match root with
      | some r =>
          match dictSetSliceWithCells (some r) bits v .set with
          | .ok (some next, _ok, _created, _loaded) =>
              root := some next
          | .ok (none, _, _, _) =>
              panic! s!"{label}: insertion unexpectedly returned none"
          | .error e =>
              panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
      | none =>
          match dictSetSliceWithCells none bits v .set with
          | .ok (some next, _ok, _created, _loaded) =>
              root := some next
          | .ok (none, _, _, _) =>
              panic! s!"{label}: initial insertion unexpectedly returned none"
          | .error e =>
              panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some c => c
    | none => panic! s!"{label}: empty dictionary fixture"

private def mkRefDictRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for e in entries do
      let (k, v) := e
      let bits := requireBits label k n
      match root with
      | some r =>
          match dictSetRefWithCells (some r) bits v .set with
          | .ok (some next, _ok, _created, _loaded) =>
              root := some next
          | .ok (none, _, _, _) =>
              panic! s!"{label}: insertion unexpectedly returned none"
          | .error e =>
              panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
      | none =>
          match dictSetRefWithCells none bits v .set with
          | .ok (some next, _ok, _created, _loaded) =>
              root := some next
          | .ok (none, _, _, _) =>
              panic! s!"{label}: initial insertion unexpectedly returned none"
          | .error e =>
              panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
    match root with
    | some c => c
    | none => panic! s!"{label}: empty dictionary fixture"

private def addSliceRoot (label : String) (root : Option Cell) (n : Nat) (key : Int) (value : Slice) : Cell :=
  match dictLookupSetSliceWithCells root (requireBits label key n) value .add with
  | .ok (_, some next, _ok, _created, _loaded) => next
  | .ok (_, none, _, _, _) =>
      panic! s!"{label}: add produced no root"
  | .error e =>
      panic! s!"{label}: dictLookupSetSliceWithCells failed: {reprStr e}"

private def addSliceCreated (label : String) (root : Option Cell) (n : Nat) (key : Int) (value : Slice) : Nat :=
  match dictLookupSetSliceWithCells root (requireBits label key n) value .add with
  | .ok (_, _, _, created, _) => created
  | .error _ => 0

private def dictSlice4 : Cell :=
  mkSliceDictRoot! "dictSlice4" 4 #[(3, sampleSliceA), (12, sampleSliceB)]
private def dictRef4 : Cell :=
  mkRefDictRoot! "dictRef4" 4 #[(3, sampleCellA), (12, sampleCellB)]
private def dictSlice4Single : Cell :=
  mkSliceDictRoot! "dictSlice4Single" 4 #[(3, sampleSliceA)]
private def dictSlice0 : Cell :=
  mkSliceDictRoot! "dictSlice0" 0 #[(0, sampleSliceC)]

private def dictSlice4InsertFromNull : Cell :=
  addSliceRoot "dictSlice4InsertFromNull" none 4 3 sampleSliceD
private def dictSlice4InsertMismatch : Cell :=
  addSliceRoot "dictSlice4InsertMismatch" (some dictSlice4Single) 4 2 sampleSliceD
private def dictSlice0Insert : Cell :=
  addSliceRoot "dictSlice0Insert" none 0 0 sampleSliceD

private def addCreatedNull : Nat :=
  addSliceCreated "addCreatedNull" none 4 3 sampleSliceD
private def addCreatedSingleMismatch : Nat :=
  addSliceCreated "addCreatedSingleMismatch" (some dictSlice4Single) 4 2 sampleSliceD
private def addCreatedZeroWidth : Nat :=
  addSliceCreated "addCreatedZeroWidth" none 0 0 sampleSliceD

private def dispatchSentinel : Int := 9_001

private def baseGas : Int :=
  computeExactGasBudget instrAdd

private def missGas : Int :=
  baseGas + Int.ofNat addCreatedNull * cellCreateGasPrice
private def mismatchGas : Int :=
  baseGas + Int.ofNat addCreatedSingleMismatch * cellCreateGasPrice
private def zeroWidthGas : Int :=
  baseGas + Int.ofNat addCreatedZeroWidth * cellCreateGasPrice
private def missGasMinusOne : Int :=
  if missGas > 0 then missGas - 1 else 0
private def mismatchGasMinusOne : Int :=
  if mismatchGas > 0 then mismatchGas - 1 else 0
private def zeroWidthGasMinusOne : Int :=
  if zeroWidthGas > 0 then zeroWidthGas - 1 else 0
private def hitGas : Int := baseGas
private def hitGasMinusOne : Int :=
  if hitGas > 0 then hitGas - 1 else 0

private def mkSliceStack (value : Value) (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[value, .slice key, dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrAdd])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pfxDictAddId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (code : Cell)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pfxDictAddId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasProgram (gas : Int) (instr : Instr) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]

private def expectDecodeStepPair (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  let s : Slice := Slice.ofCell code
  let _ ← expectDecodeStep label s expected 16
  pure ()

private def expectDecodeInv (label : String) (cell : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr} ({bits} bits)")

private def expectAssembleErr (label : String) (expected : Excno) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")

private def runPfxDictAddDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrAdd stack

private def runPfxDictAddDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrDictExt
    (.tonEnvOp .setGasLimit)
    (VM.push (intV dispatchSentinel))
    stack

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr pfxDictAddId

private def genPFXDICTADD (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 37
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow-empty" #[], rng1) -- [B2]
    else if shape = 1 then
      (mkCase "fuzz/underflow-one" #[.cell sampleCellA], rng1) -- [B2]
    else if shape = 2 then
      (mkCase "fuzz/underflow-two" #[.slice sampleSliceA, .slice (mkSliceKey 4 3)], rng1) -- [B2]
    else if shape = 3 then
      (mkCase "fuzz/underflow-three" #[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null], rng1) -- [B2]
    else if shape = 4 then
      (mkCase "fuzz/range/n-negative" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null (-1)), rng1) -- [B3]
    else if shape = 5 then
      (mkCase "fuzz/range/n-too-large" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 1024), rng1) -- [B3]
    else if shape = 6 then
      (mkCase "fuzz/range/n-nan" #[.slice sampleSliceD, .slice (mkSliceKey 4 3), .null, .int .nan], rng1) -- [B3]
    else if shape = 7 then
      (mkCase "fuzz/type/key-int" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4), rng1) -- [B4]
    else if shape = 8 then
      (mkCase "fuzz/type/value-int" (mkSliceStack (.int (.num 99)) (mkSliceKey 4 3) .null 4), rng1) -- [B4]
    else if shape = 9 then
      (mkCase "fuzz/type/dict-tuple" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.tuple #[]) 4), rng1) -- [B4]
    else if shape = 10 then
      (mkCase "fuzz/key-too-short" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 3 3) .null 4), rng1) -- [B5]
    else if shape = 11 then
      (mkCase "fuzz/key-long-noop" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 2), rng1) -- [B6]
    else if shape = 12 then
      (mkCase "fuzz/miss/null" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4), rng1) -- [B7]
    else if shape = 13 then
      (mkCase "fuzz/hit" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4), rng1) -- [B7]
    else if shape = 14 then
      (mkCase "fuzz/miss/non-null" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 2) (.cell dictSlice4Single) 4), rng1) -- [B7]
    else if shape = 15 then
      (mkCase "fuzz/mismatch" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 2) (.cell dictSlice4Single) 4), rng1) -- [B7]
    else if shape = 16 then
      (mkCase "fuzz/malformed-root" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell malformedCell) 4), rng1) -- [B8]
    else if shape = 17 then
      (mkCase "fuzz/malformed-ref-root" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell malformedCell) 4), rng1) -- [B8]
    else if shape = 18 then
      (mkCodeCase "fuzz/decode/470" raw470, rng1) -- [B10]
    else if shape = 19 then
      (mkCodeCase "fuzz/decode/471" raw471, rng1) -- [B10]
    else if shape = 20 then
      (mkCodeCase "fuzz/decode/472" raw472, rng1) -- [B10]
    else if shape = 21 then
      (mkCodeCase "fuzz/decode/473" raw473, rng1) -- [B10]
    else if shape = 22 then
      (mkCodeCase "fuzz/decode/46c" raw46C, rng1) -- [B10]
    else if shape = 23 then
      (mkCodeCase "fuzz/decode/trunc8" rawF4, rng1) -- [B10]
    else if shape = 24 then
      (mkCase "fuzz/gas/miss-exact"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)
        (mkGasProgram missGas instrAdd) (oracleGasLimitsExact missGas), rng1) -- [B11]
    else if shape = 25 then
      (mkCase "fuzz/gas/miss-exact-minus-one"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)
        (mkGasProgram missGasMinusOne instrAdd) (oracleGasLimitsExact missGasMinusOne), rng1) -- [B11]
    else if shape = 26 then
      (mkCase "fuzz/gas/hit-exact"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
        (mkGasProgram hitGas instrAdd) (oracleGasLimitsExact hitGas), rng1) -- [B11]
    else if shape = 27 then
      (mkCase "fuzz/gas/hit-exact-minus-one"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
        (mkGasProgram hitGasMinusOne instrAdd) (oracleGasLimitsExact hitGasMinusOne), rng1) -- [B11]
    else if shape = 28 then
      (mkCase "fuzz/gas/mismatch-exact"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 2) (.cell dictSlice4Single) 4)
        (mkGasProgram mismatchGas instrAdd) (oracleGasLimitsExact mismatchGas), rng1) -- [B11]
    else if shape = 29 then
      (mkCase "fuzz/gas/mismatch-exact-minus-one"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 2) (.cell dictSlice4Single) 4)
        (mkGasProgram mismatchGasMinusOne instrAdd) (oracleGasLimitsExact mismatchGasMinusOne), rng1) -- [B11]
    else if shape = 30 then
      (mkCase "fuzz/gas/zero-width-exact"
        (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0)
        (mkGasProgram zeroWidthGas instrAdd) (oracleGasLimitsExact zeroWidthGas), rng1) -- [B11]
    else if shape = 31 then
      (mkCase "fuzz/gas/zero-width-exact-minus-one"
        (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0)
        (mkGasProgram zeroWidthGasMinusOne instrAdd) (oracleGasLimitsExact zeroWidthGasMinusOne), rng1) -- [B11]
    else if shape = 32 then
      (mkCase "fuzz/asm-invalid"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
        #[.dictSet false false false .replace], rng1) -- [B9]
    else if shape = 33 then
      (mkCase "fuzz/zero-width-non-null-hit"
        (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0)
        , rng1) -- [B7]
    else if shape = 34 then
      (mkCase "fuzz/zero-width-insert-non-null"
        (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0)
        , rng1) -- [B7]
    else if shape = 35 then
      (mkCase "fuzz/key-too-short-on-zero-width" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 1), rng1) -- [B5]
    else if shape = 36 then
      (mkCase "fuzz/random-36" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4), rng1)
    else
      (mkCase "fuzz/random-37" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := pfxDictAddId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "unit/dispatch/fallback"
          (runPfxDictAddDispatchFallback #[])
          #[intV dispatchSentinel] },

    { name := "unit/asm/invalid-dictset"
      run := do
        expectAssembleErr "unit/asm/invalid-dictset" .invOpcode (.dictSet false true false .replace) }, -- [B9]

    { name := "unit/decode/472" -- [B10]
      run := do
        expectDecodeStepPair "unit/decode/472" raw472 (.dictExt (.pfxSet .add)) },

    { name := "unit/decode/alias/470" -- [B10]
      run := do
        expectDecodeStepPair "unit/decode/470" raw470 (.dictExt (.pfxSet .set)) },

    { name := "unit/decode/alias/471" -- [B10]
      run := do
        expectDecodeStepPair "unit/decode/471" raw471 (.dictExt (.pfxSet .replace)) },

    { name := "unit/decode/alias/473" -- [B10]
      run := do
        expectDecodeStepPair "unit/decode/473" raw473 (.dictExt .pfxDel) },

    { name := "unit/decode/invalid-neighbors" -- [B10]
      run := do
        expectDecodeInv "unit/decode/46c" raw46C
        expectDecodeInv "unit/decode/truncated" rawF4 },

    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runPfxDictAddDirect #[]) .stkUnd },

    { name := "unit/runtime/underflow-one" -- [B2]
      run := do
        expectErr "underflow-one" (runPfxDictAddDirect #[.cell sampleCellA]) .stkUnd },

    { name := "unit/runtime/underflow-two" -- [B2]
      run := do
        expectErr "underflow-two" (runPfxDictAddDirect (#[.slice sampleSliceA, .slice (mkSliceKey 4 3)])) .stkUnd },

    { name := "unit/runtime/underflow-three" -- [B2]
      run := do
        expectErr "underflow-three" (runPfxDictAddDirect (#[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null])) .stkUnd },

    { name := "unit/runtime/range/n-negative" -- [B3]
      run := do
        expectErr "n-negative" (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null (-1))) .rangeChk },

    { name := "unit/runtime/range/n-too-large" -- [B3]
      run := do
        expectErr "n-too-large" (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 1024)) .rangeChk },

    { name := "unit/runtime/range/n-nan" -- [B3]
      run := do
        expectErr "n-nan" (runPfxDictAddDirect (#[.slice sampleSliceD, .slice (mkSliceKey 4 3), .null, .int .nan])) .rangeChk },

    { name := "unit/runtime/type/key-int" -- [B4]
      run := do
        expectErr "key-int" (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)) .typeChk },

    { name := "unit/runtime/type/value-int" -- [B4]
      run := do
        expectErr "value-int" (runPfxDictAddDirect (mkSliceStack (.int (.num 77)) (mkSliceKey 4 3) .null 4)) .typeChk },

    { name := "unit/runtime/type/dict-tuple" -- [B4]
      run := do
        expectErr "dict-tuple" (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.tuple #[]) 4)) .typeChk },

    { name := "unit/runtime/key-too-short" -- [B5]
      run := do
        expectErr "key-too-short" (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceA) (mkSliceKey 3 3) .null 4)) .cellUnd },

    { name := "unit/runtime/key-too-long-truncated-no-op" -- [B6]
      run := do
        expectOkStack
          "unit/runtime/key-too-long"
          (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 2))
          #[.cell dictSlice4, intV 0] },

    { name := "unit/runtime/miss-null" -- [B7]
      run := do
        expectOkStack
          "unit/runtime/miss-null"
          (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4))
          #[.cell dictSlice4InsertFromNull, intV (-1)] },

    { name := "unit/runtime/miss-nonnull" -- [B7]
      run := do
        expectOkStack
          "unit/runtime/miss-nonnull"
          (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 7) (.cell dictSlice4Single) 4))
          #[.cell dictSlice4InsertMismatch, intV (-1)] },

    { name := "unit/runtime/hit" -- [B7]
      run := do
        expectOkStack
          "unit/runtime/hit"
          (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4))
          #[.cell dictSlice4, intV 0] },

    { name := "unit/runtime/zero-width-hit" -- [B7]
      run := do
        expectOkStack
          "unit/runtime/zero-width-hit"
          (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0))
          #[.cell dictSlice0, intV 0] },

    { name := "unit/runtime/zero-width-miss" -- [B7]
      run := do
        expectOkStack
          "unit/runtime/zero-width-miss"
          (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0))
          #[.cell dictSlice0Insert, intV (-1)] },

    { name := "unit/runtime/dict-err" -- [B8]
      run := do
        expectErr "dict-err" (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell malformedCell) 4)) .dictErr },

    { name := "unit/runtime/ref-dict-hit" -- [B7]
      run := do
        expectOkStack
          "unit/runtime/ref-dict-hit"
          (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictRef4) 4))
          #[.cell dictRef4, intV 0] },

    { name := "unit/runtime/gas/miss-exact" -- [B11]
      run := do
        expectOkStack
          "unit/runtime/gas/miss-exact"
          (runPfxDictAddDirect (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4))
          #[.cell dictSlice4InsertFromNull, intV (-1)] }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow-empty" #[],
    mkCase "oracle/underflow-one" #[.cell sampleCellA],
    mkCase "oracle/underflow-two" #[.slice sampleSliceA, .slice (mkSliceKey 4 3)],
    mkCase "oracle/underflow-three" #[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null],

    -- [B3]
    mkCase "oracle/range/n-negative" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null (-1)),
    mkCase "oracle/range/n-too-large" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 1024),
    mkCase "oracle/range/n-nan" #[.slice sampleSliceD, .slice (mkSliceKey 4 3), .null, .int .nan],

    -- [B4]
    mkCase "oracle/type/key-int" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4),
    mkCase "oracle/type/value-int" (mkSliceStack (.int (.num 77)) (mkSliceKey 4 3) .null 4),
    mkCase "oracle/type/dict-tuple" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.tuple #[]) 4),

    -- [B5]
    mkCase "oracle/key-too-short" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 3 3) .null 4),

    -- [B6]
    mkCase "oracle/key-too-long-no-op" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 2),

    -- [B7]
    mkCase "oracle/miss-null" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4),
    mkCase "oracle/miss-nonnull-single" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 7) (.cell dictSlice4Single) 4),
    mkCase "oracle/hit" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4),
    mkCase "oracle/zero-width-hit" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0),
    mkCase "oracle/zero-width-miss" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0),
    mkCase "oracle/ref-dict-hit" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictRef4) 4),

    -- [B8]
    mkCase "oracle/dict-err" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell malformedCell) 4),

    -- [B9]
    mkCase "oracle/asm-invalid" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4) (#[.dictSet false true false .replace]),

    -- [B10]
    mkCodeCase "oracle/decode/472" raw472,
    mkCodeCase "oracle/decode/470" raw470,
    mkCodeCase "oracle/decode/471" raw471,
    mkCodeCase "oracle/decode/473" raw473,
    mkCodeCase "oracle/decode/46c" raw46C,
    mkCodeCase "oracle/decode/trunc8" rawF4,

    -- [B11]
    mkCase "oracle/gas/miss-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGas instrAdd)
      (oracleGasLimitsExact missGas),
    mkCase "oracle/gas/miss-exact-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasMinusOne instrAdd)
      (oracleGasLimitsExact missGasMinusOne),
    mkCase "oracle/gas/hit-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
      (mkGasProgram hitGas instrAdd)
      (oracleGasLimitsExact hitGas),
    mkCase "oracle/gas/hit-exact-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
      (mkGasProgram hitGasMinusOne instrAdd)
      (oracleGasLimitsExact hitGasMinusOne),
    mkCase "oracle/gas/mismatch-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 2) (.cell dictSlice4Single) 4)
      (mkGasProgram mismatchGas instrAdd)
      (oracleGasLimitsExact mismatchGas),
    mkCase "oracle/gas/mismatch-exact-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 2) (.cell dictSlice4Single) 4)
      (mkGasProgram mismatchGasMinusOne instrAdd)
      (oracleGasLimitsExact mismatchGasMinusOne),
    mkCase "oracle/gas/zero-width-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0)
      (mkGasProgram zeroWidthGas instrAdd)
      (oracleGasLimitsExact zeroWidthGas),
    mkCase "oracle/gas/zero-width-exact-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0)
      (mkGasProgram zeroWidthGasMinusOne instrAdd)
      (oracleGasLimitsExact zeroWidthGasMinusOne),

    mkCase "oracle/range-maximum-n" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 3 5) (.cell dictSlice4) 1023),
    mkCase "oracle/range-zero-n" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0),
    mkCase "oracle/type-key-short-for-0" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice4Single) 4)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genPFXDICTADD }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTADD
