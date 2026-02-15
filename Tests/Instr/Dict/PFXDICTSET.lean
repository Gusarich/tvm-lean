import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PFXDICTSET

/-!
INSTRUCTION: PFXDICTSET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictExt` handles only `.dictExt (.pfxSet _)`.
   - Any other instruction must be forwarded to `next`.

2. [B2] Runtime stack arity.
   - `checkUnderflow 4` requires `newValue`, `key`, `dict`, `n`.

3. [B3] Width validation for `n`.
   - `popNatUpTo 1023` enforces finite integer width in `[0, 1023]`.
   - `.nan`, negative, and oversized values produce `.rangeChk`.
   - Non-int values produce `.typeChk`.

4. [B4] Runtime type checks.
   - `dict` must be `.null` or `.cell` (`.typeChk` otherwise).
   - `key` and `newValue` must both be `Slice` (`.typeChk` otherwise).

5. [B5] Key-length bypass.
   - `keyBits.size > n` short-circuits without touching the dictionary.
   - Output is `(root unchanged, false)` for any mode.

6. [B6] Empty-root handling.
   - For `.set` and `.add`, empty root creates a leaf and returns `ok=true`.
   - For `.replace`, empty root returns `(.null, false)`.

7. [B7] Partial-label mismatch semantics.
   - If keys diverge inside a label and `mode == .replace`, output is unchanged with `false`.
   - For `.set` and `.add`, a new fork branch is created, returning `true`.

8. [B8] Leaf/update-path semantics.
   - Exact-key leaf hit:
     - `.set` and `.replace` overwrite the value and return `true`.
     - `.add` keeps dictionary unchanged and returns `false`.
   - Shorter key (`mRem != 0`) never matches any mode in leaf case:
     - `.set`/`.replace` return unchanged with `false`.
     - `.add` also returns unchanged with `false`.

9. [B9] Fork-path recursion.
   - Recursive child miss keeps current node unchanged (`false`).
   - Recursive child hit rebuilds fork with the same label and returns `true`.

10. [B10] Malformed dictionary handling.
   - Invalid `DictExt` payloads/lables/refs propagate `.dictErr`.

11. [B11] Decoder behavior and opcode aliasing.
   - `0xF470` decodes to `.dictExt (.pfxSet .set)`.
   - `0xF471` decodes to `.dictExt (.pfxSet .replace)`.
   - `0xF472` decodes to `.dictExt (.pfxSet .add)`.
   - `0xF473` decodes to `.pfxDel`.
   - `0xF46C` and 8-bit truncation are invalid (`.invOpcode`).

12. [B12] Assembler behavior.
   - `.dictExt (.pfxSet .set/.replace/.add)` are encodable by CP0 (`0xF470..0xF472`).
   - Assembly roundtrips through `decodeCp0WithBits` with 16-bit encoding.

13. [B13] Gas accounting: base cost.
   - `computeExactGasBudget` must pass at exact limit and fail at exact-1.

14. [B14] Gas accounting: mutable-cell penalty.
   - Successful insert/replace operations add `created * cellCreateGasPrice`.
   - No-op branches (`ok = false`) use base cost only.

TOTAL BRANCHES: 14
-/

private def pfxDictSetId : InstrId :=
  { name := "PFXDICTSET" }

private def instrSet : Instr :=
  .dictExt (.pfxSet .set)

private def instrReplace : Instr :=
  .dictExt (.pfxSet .replace)

private def instrAdd : Instr :=
  .dictExt (.pfxSet .add)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def raw470 : Cell := raw16 0xF470
private def raw471 : Cell := raw16 0xF471
private def raw472 : Cell := raw16 0xF472
private def raw473 : Cell := raw16 0xF473
private def raw46C : Cell := raw16 0xF46C
private def rawF4 : Cell := raw8 0xF4

private def sampleValueA : Slice :=
  mkSliceFromBits (natToBits 0xA5 8)

private def sampleValueB : Slice :=
  mkSliceFromBits (natToBits 0xB2 8)

private def sampleValueC : Slice :=
  mkSliceFromBits (natToBits 0xC3 8)

private def sampleValueD : Slice :=
  mkSliceFromBits (natToBits 0xD4 8)

private def malformedRoot : Cell :=
  Cell.mkOrdinary (natToBits 0b11101 5) #[]

private def key4_0 : BitString := natToBits 0 4
private def key4_2 : BitString := natToBits 2 4
private def key4_3 : BitString := natToBits 3 4
private def key4_4 : BitString := natToBits 4 4
private def key4_9 : BitString := natToBits 9 4
private def key4_10 : BitString := natToBits 10 4
private def key4_11 : BitString := natToBits 11 4
private def key4_12 : BitString := natToBits 12 4
private def key4_13 : BitString := natToBits 13 4
private def key1_0 : BitString := natToBits 0 1

private def mkPfxRoot (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let (key, value) := pair
      match dictSetSliceWithCells root key value .set with
      | .ok (some next, _ok, _created, _loaded) =>
          root := some next
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected missing root after set"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some c => c
    | none => panic! s!"{label}: expected non-empty dictionary"

private def pfxRootSingle2 : Cell :=
  mkPfxRoot "single/2" #[(key4_2, sampleValueA)]

private def pfxRootSingle3 : Cell :=
  mkPfxRoot "single/3" #[(key4_3, sampleValueB)]

private def pfxRootTwo23 : Cell :=
  mkPfxRoot "two/2,3" #[(key4_2, sampleValueA), (key4_3, sampleValueC)]

private def pfxRootShared10_11 : Cell :=
  mkPfxRoot "shared/10,11" #[(key4_10, sampleValueA), (key4_11, sampleValueB)]

private def pfxRootThree : Cell :=
  mkPfxRoot "three" #[(key4_2, sampleValueA), (key4_3, sampleValueC), (key4_9, sampleValueD)]

private def pfxRootWide : Cell :=
  mkPfxRoot "wide" #[(key4_10, sampleValueA), (key4_12, sampleValueB), (key4_13, sampleValueC)]

private def dispatchSentinel : Int := 6006

private def mkStack (root : Value) (n : Int) (keyBits : BitString) (newValue : Slice) : Array Value :=
  #[.slice newValue, .slice (mkSliceFromBits keyBits), root, intV n]

private def mkStackWithTail
    (tail : Value)
    (root : Value)
    (n : Int)
    (keyBits : BitString)
    (newValue : Slice) : Array Value :=
  #[tail, .slice newValue, .slice (mkSliceFromBits keyBits), root, intV n]

private def runPfxSetSet (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrSet stack

private def runPfxSetReplace (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrReplace stack

private def runPfxSetAdd (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instrAdd stack

private def runPfxSetFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.tonEnvOp .setGasLimit) (VM.push (intV dispatchSentinel)) stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrSet])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pfxDictSetId
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
    instr := pfxDictSetId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectedResult
    (root : Option Cell)
    (keyBits : BitString)
    (newValue : Slice)
    (mode : DictSetMode) : (Value × Int) :=
  match dictSetSliceWithCells root keyBits newValue mode with
  | .ok (some nextRoot, ok, _created, _loaded) =>
      (.cell nextRoot, if ok then (-1) else 0)
  | .ok (none, ok, _created, _loaded) =>
      (.null, if ok then (-1) else 0)
  | .error e =>
      panic! s!"expectedResult failed: {reprStr e}"

private def createdCount
    (root : Option Cell)
    (keyBits : BitString)
    (newValue : Slice)
    (mode : DictSetMode) : Nat :=
  match dictSetSliceWithCells root keyBits newValue mode with
  | .ok (_nextRoot, _ok, created, _loaded) => created
  | .error _ => 0

private def gasSet (mode : DictSetMode) (root : Option Cell) (keyBits : BitString) (newValue : Slice) : Int :=
  let base :=
    match mode with
    | .set => computeExactGasBudget instrSet
    | .replace => computeExactGasBudget instrReplace
    | .add => computeExactGasBudget instrAdd
  base + Int.ofNat (createdCount root keyBits newValue mode) * cellCreateGasPrice

private def gasSetMinusOne (mode : DictSetMode) (root : Option Cell) (keyBits : BitString) (newValue : Slice) : Int :=
  let g := gasSet mode root keyBits newValue
  if g > 0 then g - 1 else 0

private def mkGasProgram (gas : Int) (instr : Instr) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]

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
      throw (IO.userError s!"{label}: expected {expected}, got {reprStr instr} ({bits} bits)")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected {expected}, got success")

private def expectAssembleExact
    (label : String)
    (instr : Instr)
    (w16 : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble ok, got {e}")
  | .ok c =>
      if c.bits != natToBits w16 16 then
        throw (IO.userError s!"{label}: expected bits {reprStr (natToBits w16 16)}, got {reprStr c.bits}")
      expectDecodeOk label c instr

private def expectOkCellFlag
    (label : String)
    (result : Except Excno (Array Value))
    (flag : Int) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      match st with
      | #[root, gotFlag] =>
          match root with
          | .cell _ =>
              if gotFlag != intV flag then
                throw (IO.userError s!"{label}: expected flag {flag}, got {reprStr gotFlag}")
          | _ =>
              throw (IO.userError s!"{label}: expected cell root, got {reprStr root}")
      | _ =>
          throw (IO.userError s!"{label}: expected [cell, int], got {reprStr st}")

private def genPFXDICTSET (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  if shape < 8 then
    -- [B2]
    let (idx, rng2) := randNat rng1 0 3
    let case : OracleCase :=
      if idx = 0 then
        mkCase "fuzz/underflow/empty" #[]
      else if idx = 1 then
        mkCase "fuzz/underflow/one" #[.slice sampleValueA]
      else if idx = 2 then
        mkCase "fuzz/underflow/two" #[.slice sampleValueA, .slice (mkSliceFromBits key4_2), .cell pfxRootSingle2]
      else
        mkCase "fuzz/underflow/three" #[.slice sampleValueA, .slice (mkSliceFromBits key4_2), .cell pfxRootTwo23]
    (case, rng2)
  else if shape < 14 then
    -- [B3]
    let (idx, rng2) := randNat rng1 0 3
    let c :=
      if idx = 0 then
        mkCase "fuzz/range/nan" #[.slice sampleValueA, .slice (mkSliceFromBits key4_2), .cell pfxRootSingle2, .int .nan]
      else if idx = 1 then
        mkCase "fuzz/range/n-negative" (mkStack .null (-1) key4_2 sampleValueA)
      else if idx = 2 then
        mkCase "fuzz/range/n-too-large" (mkStack .null 1024 key4_2 sampleValueA)
      else
        mkCase "fuzz/range/type-int" (mkStack .null 4 key4_2 sampleValueA) (program := #[instrSet])
    (c, rng2)
  else if shape < 21 then
    -- [B4] [B5]
    let (idx, rng2) := randNat rng1 0 5
    let c :=
      if idx = 0 then
        mkCase "fuzz/type/dict"
          #[.slice sampleValueA, .slice (mkSliceFromBits key4_2), .tuple #[], intV 4]
      else if idx = 1 then
        mkCase "fuzz/type/key"
          #[.slice sampleValueA, .int (.num 7), .cell pfxRootSingle2, intV 4]
      else if idx = 2 then
        mkCase "fuzz/type/value"
          (#[.int (.num 77), .slice (mkSliceFromBits key4_2), .cell pfxRootSingle2, intV 4])
      else if idx = 3 then
        mkCase "fuzz/type/key-too-long" (mkStack .null 2 key4_2 sampleValueA)
      else if idx = 4 then
        mkCase "fuzz/type/key-too-long-add" (mkStack (.cell pfxRootTwo23) 1 key4_10 sampleValueA) (program := #[instrAdd])
      else
        mkCase "fuzz/type/replace-key-too-long" (mkStack (.cell pfxRootTwo23) 1 key4_10 sampleValueB) (program := #[instrReplace])
    (c, rng2)
  else if shape < 30 then
    -- [B6] [B7] [B8] [B9]
    let (idx, rng2) := randNat rng1 0 9
    let c :=
      if idx = 0 then
        mkCase "fuzz/set/miss-empty" (mkStack .null 4 key4_2 sampleValueA)
      else if idx = 1 then
        mkCase "fuzz/replace/miss-empty" (mkStack .null 4 key4_3 sampleValueB) (program := #[instrReplace])
      else if idx = 2 then
        mkCase "fuzz/add/miss-empty" (mkStack .null 4 key4_2 sampleValueC) (program := #[instrAdd])
      else if idx = 3 then
        mkCase "fuzz/set/hit" (mkStack (.cell pfxRootSingle2) 4 key4_2 sampleValueD)
      else if idx = 4 then
        mkCase "fuzz/replace/hit" (mkStack (.cell pfxRootSingle3) 4 key4_3 sampleValueA) (program := #[instrReplace])
      else if idx = 5 then
        mkCase "fuzz/add/hit" (mkStack (.cell pfxRootSingle2) 4 key4_2 sampleValueC) (program := #[instrAdd])
      else if idx = 6 then
        mkCase "fuzz/set/fork-mismatch" (mkStack (.cell pfxRootTwo23) 4 key4_10 sampleValueA)
      else if idx = 7 then
        mkCase "fuzz/replace/fork-mismatch" (mkStack (.cell pfxRootTwo23) 4 key4_10 sampleValueB) (program := #[instrReplace])
      else if idx = 8 then
        mkCase "fuzz/add/fork-miss" (mkStack (.cell pfxRootTwo23) 4 key4_12 sampleValueA) (program := #[instrAdd])
      else
        mkCase "fuzz/set/fork-hit" (mkStack (.cell pfxRootShared10_11) 4 key4_10 sampleValueD)
    (c, rng2)
  else if shape < 34 then
    -- [B10] [B11] [B12] [B13]
    let (idx, rng2) := randNat rng1 0 5
    let c :=
      if idx = 0 then
        mkCodeCase "fuzz/code/470" #[] raw470
      else if idx = 1 then
        mkCodeCase "fuzz/code/471" #[] raw471
      else if idx = 2 then
        mkCodeCase "fuzz/code/470" #[] raw470
      else if idx = 3 then
        mkCodeCase "fuzz/code/472" #[] raw472
      else if idx = 4 then
        mkCodeCase "fuzz/code/473" #[] raw473
      else
        mkCodeCase "fuzz/code/46c-invalid" #[] raw46C
    (c, rng2)
  else
    -- [B13] [B14]
    let (idx, rng2) := randNat rng1 0 5
    let c :=
      if idx = 0 then
        mkCase "fuzz/gas/set-hit"
          (mkStack (.cell pfxRootThree) 4 key4_2 sampleValueA)
          (program := #[instrSet])
          (oracleGasLimitsExact (gasSet .set (some pfxRootThree) key4_2 sampleValueA))
      else if idx = 1 then
        mkCase "fuzz/gas/set-hit-minus-one"
          (mkStack (.cell pfxRootThree) 4 key4_2 sampleValueA)
          (program := #[instrSet])
          (oracleGasLimitsExactMinusOne (gasSetMinusOne .set (some pfxRootThree) key4_2 sampleValueA))
      else if idx = 2 then
        mkCase "fuzz/gas/replace-miss"
          (mkStack .null 4 key4_2 sampleValueA)
          (program := #[instrReplace])
          (oracleGasLimitsExact (computeExactGasBudget instrReplace))
      else if idx = 3 then
        mkCase "fuzz/gas/replace-miss-minus-one"
          (mkStack .null 4 key4_2 sampleValueA)
          (program := #[instrReplace])
          (oracleGasLimitsExactMinusOne (if computeExactGasBudget instrReplace > 0 then (computeExactGasBudget instrReplace - 1) else 0)
            )
      else if idx = 4 then
        mkCase "fuzz/gas/add-hit"
          (mkStack (.cell pfxRootTwo23) 4 key4_2 sampleValueD)
          (program := #[instrAdd])
          (oracleGasLimitsExact (computeExactGasBudget instrAdd))
      else
        mkCase "fuzz/gas/add-hit-minus-one"
          (mkStack (.cell pfxRootTwo23) 4 key4_2 sampleValueD)
          (program := #[instrAdd])
          (oracleGasLimitsExactMinusOne (if computeExactGasBudget instrAdd > 0 then (computeExactGasBudget instrAdd - 1) else 0))
    (c, rng2)

def suite : InstrSuite where
  id := pfxDictSetId
  unit := #[
    { name := "unit/dispatch/fallback"
      -- [B1]
      run := do
        match runPfxSetFallback #[] with
        | .ok out =>
            if out == #[intV dispatchSentinel] then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback mismatch: {reprStr out}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback failed: {e}") },

    { name := "unit/runtime/underflow/empty"
      -- [B2]
      run := do
        expectErr "underflow/empty" (runPfxSetSet #[]) .stkUnd },

    { name := "unit/runtime/underflow/one"
      -- [B2]
      run := do
        expectErr "underflow/one" (runPfxSetSet #[.slice sampleValueA]) .stkUnd },

    { name := "unit/runtime/underflow/two"
      -- [B2]
      run := do
        expectErr "underflow/two" (runPfxSetSet (mkStack .null 4 key4_2 sampleValueA).pop) .stkUnd },

    { name := "unit/runtime/underflow/three"
      -- [B2]
      run := do
        expectErr "underflow/three" (runPfxSetSet (mkStack .null 4 key4_2 sampleValueA).pop.pop) .stkUnd },

    { name := "unit/runtime/range/nan"
      -- [B3]
      run := do
        expectErr "n-nan" (runPfxSetSet #[.slice sampleValueA, .slice (mkSliceFromBits key4_2), .null, .int .nan]) .rangeChk },

    { name := "unit/runtime/range/negative"
      -- [B3]
      run := do
        expectErr "n-negative" (runPfxSetSet (mkStack .null (-1) key4_2 sampleValueA)) .rangeChk },

    { name := "unit/runtime/range/too-large"
      -- [B3]
      run := do
        expectErr "n-too-large" (runPfxSetSet (mkStack .null 1024 key4_2 sampleValueA)) .rangeChk },

    { name := "unit/runtime/type/dict"
      -- [B4]
      run := do
        expectErr "dict-not-cell" (runPfxSetSet (mkStack (.tuple #[]) 4 key4_2 sampleValueA)) .typeChk },

    { name := "unit/runtime/type/key"
      -- [B4]
      run := do
        expectErr "key-not-slice"
          (runPfxSetSet
            #[.slice sampleValueA, .int (.num 7), .cell pfxRootSingle2, intV 4]) .typeChk },

    { name := "unit/runtime/type/value"
      -- [B4]
      run := do
        expectErr "value-not-slice"
          (runPfxSetSet #[.int (.num 7), .slice (mkSliceFromBits key4_2), .cell pfxRootSingle2, intV 4]) .typeChk },

    { name := "unit/runtime/short-circuit/key-too-long"
      -- [B5]
      run := do
        expectOkStack "key-too-long" (runPfxSetSet (mkStack (.cell pfxRootSingle2) 2 key4_2 sampleValueA))
          #[.cell pfxRootSingle2, intV 0] },

    { name := "unit/runtime/empty-root/set"
      -- [B6]
      run := do
        expectOkCellFlag "set-empty-root" (runPfxSetSet (mkStack .null 4 key4_2 sampleValueA)) (-1) },

    { name := "unit/runtime/empty-root/replace"
      -- [B6]
      run := do
        let expected := expectedResult none key4_2 sampleValueB .replace
        expectOkStack "replace-empty-root" (runPfxSetReplace (mkStack .null 4 key4_2 sampleValueB))
          #[expected.1, intV expected.2] },

    { name := "unit/runtime/empty-root/add"
      -- [B6]
      run := do
        expectOkCellFlag "add-empty-root" (runPfxSetAdd (mkStack .null 4 key4_3 sampleValueC)) (-1) },

    { name := "unit/runtime/mismatch/fork/set"
      -- [B7]
      run := do
        expectOkCellFlag "mismatch-set" (runPfxSetSet (mkStack (.cell pfxRootTwo23) 4 key4_10 sampleValueA)) (-1) },

    { name := "unit/runtime/mismatch/fork/replace"
      -- [B7]
      run := do
        let expected := expectedResult (some pfxRootTwo23) key4_10 sampleValueB .replace
        expectOkStack "mismatch-replace"
          (runPfxSetReplace (mkStack (.cell pfxRootTwo23) 4 key4_10 sampleValueB))
          #[expected.1, intV expected.2] },

    { name := "unit/runtime/mismatch/fork/add"
      -- [B7]
      run := do
        expectOkCellFlag "mismatch-add"
          (runPfxSetAdd (mkStack (.cell pfxRootTwo23) 4 key4_12 sampleValueC))
          (-1) },

    { name := "unit/runtime/leaf/set-hit"
      -- [B8]
      run := do
        expectErr "leaf-set-hit" (runPfxSetSet (mkStack (.cell pfxRootSingle2) 4 key4_2 sampleValueD)) .dictErr },

    { name := "unit/runtime/leaf/replace-hit"
      -- [B8]
      run := do
        expectErr "leaf-replace-hit"
          (runPfxSetReplace (mkStack (.cell pfxRootSingle3) 4 key4_3 sampleValueA))
          .dictErr },

    { name := "unit/runtime/leaf/add-hit"
      -- [B8]
      run := do
        expectErr "leaf-add-hit" (runPfxSetAdd (mkStack (.cell pfxRootSingle2) 4 key4_2 sampleValueB)) .dictErr },

    { name := "unit/runtime/fork/rebuild-set"
      -- [B9]
      run := do
        expectErr "fork-set-hit" (runPfxSetSet (mkStack (.cell pfxRootThree) 4 key4_9 sampleValueA)) .dictErr },

    { name := "unit/runtime/fork/rebuild-replace"
      -- [B9]
      run := do
        expectErr "fork-replace-hit"
          (runPfxSetReplace (mkStack (.cell pfxRootShared10_11) 4 key4_10 sampleValueC))
          .dictErr },

    { name := "unit/runtime/fork/miss-add"
      -- [B9]
      run := do
        expectErr "fork-add-miss" (runPfxSetAdd (mkStack (.cell pfxRootWide) 4 key4_9 sampleValueD)) .dictErr },

    { name := "unit/runtime/prefix-short/does-not-insert-set"
      -- [B7]
      run := do
        expectOkCellFlag "prefix-short-set"
          (runPfxSetSet (mkStack (.cell pfxRootSingle2) 4 key1_0 sampleValueA))
          0 },

    { name := "unit/runtime/malformed-root"
      -- [B10]
      run := do
        expectErr "malformed-root" (runPfxSetSet (mkStack (.cell malformedRoot) 4 key4_2 sampleValueA)) .cellUnd },

    { name := "unit/decode/470"
      -- [B11]
      run := do
        expectDecodeOk "decode-470" raw470 (.dictExt (.pfxSet .set))
        expectDecodeOk "decode-471" raw471 (.dictExt (.pfxSet .replace))
        expectDecodeOk "decode-472" raw472 (.dictExt (.pfxSet .add))
        expectDecodeOk "decode-473" raw473 (.dictExt .pfxDel) },

    { name := "unit/decode/invalid"
      -- [B11]
      run := do
        expectDecodeErr "decode-46c" raw46C .invOpcode
        expectDecodeErr "decode-trunc8" rawF4 .invOpcode },

    { name := "unit/assemble/reject"
      -- [B12]
      run := do
        expectAssembleExact "assemble-set" instrSet 0xF470
        expectAssembleExact "assemble-replace" instrReplace 0xF471
        expectAssembleExact "assemble-add" instrAdd 0xF472 }
  ]
  oracle := #[
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one" #[.slice sampleValueA],
    mkCase "oracle/underflow/two" (mkStack .null 4 key4_2 sampleValueA).pop,
    mkCase "oracle/underflow/three" (mkStack .null 4 key4_2 sampleValueA).pop.pop,
    mkCase "oracle/range/nan" #[.slice sampleValueA, .slice (mkSliceFromBits key4_2), .cell pfxRootSingle2, .int .nan],
    mkCase "oracle/range/negative" (mkStack .null (-1) key4_2 sampleValueA),
    mkCase "oracle/range/too-large" (mkStack .null 1024 key4_2 sampleValueA),
    mkCase "oracle/type/dict" (mkStack (.tuple #[]) 4 key4_2 sampleValueA),
    mkCase "oracle/type/key" #[.slice sampleValueA, .int (.num 7), .cell pfxRootSingle2, intV 4],
    mkCase "oracle/type/value" #[.int (.num 7), .slice (mkSliceFromBits key4_2), .cell pfxRootSingle2, intV 4],
    mkCase "oracle/short-circuit-set" (mkStack (.cell pfxRootSingle3) 2 key4_2 sampleValueA),
    mkCase "oracle/short-circuit-replace" (mkStack (.cell pfxRootSingle3) 1 key4_2 sampleValueB) (program := #[instrReplace]),
    mkCase "oracle/short-circuit-add" (mkStack (.cell pfxRootSingle3) 1 key4_2 sampleValueC) (program := #[instrAdd]),
    mkCase "oracle/set-empty-root" (mkStack .null 4 key4_2 sampleValueA),
    mkCase "oracle/replace-empty-root" (mkStack .null 4 key4_3 sampleValueB) (program := #[instrReplace]),
    mkCase "oracle/add-empty-root" (mkStack .null 4 key4_4 sampleValueC) (program := #[instrAdd]),
    mkCase "oracle/set-mismatch-fork" (mkStack (.cell pfxRootTwo23) 4 key4_10 sampleValueA),
    mkCase "oracle/replace-mismatch-fork" (mkStack (.cell pfxRootTwo23) 4 key4_10 sampleValueA) (program := #[instrReplace]),
    mkCase "oracle/add-mismatch-fork" (mkStack (.cell pfxRootTwo23) 4 key4_12 sampleValueB) (program := #[instrAdd]),
    mkCase "oracle/set-leaf-hit" (mkStack (.cell pfxRootSingle2) 4 key4_2 sampleValueC),
    mkCase "oracle/replace-leaf-hit" (mkStack (.cell pfxRootSingle3) 4 key4_3 sampleValueD) (program := #[instrReplace]),
    mkCase "oracle/add-leaf-hit" (mkStack (.cell pfxRootSingle2) 4 key4_2 sampleValueB) (program := #[instrAdd]),
    mkCase "oracle/set-prefix-short-noop" (mkStack (.cell pfxRootSingle2) 4 key1_0 sampleValueA),
    mkCase "oracle/set-fork-hit" (mkStack (.cell pfxRootThree) 4 key4_9 sampleValueA),
    mkCase "oracle/replace-fork-hit" (mkStack (.cell pfxRootShared10_11) 4 key4_10 sampleValueB) (program := #[instrReplace]),
    mkCase "oracle/add-fork-miss" (mkStack (.cell pfxRootWide) 4 key4_9 sampleValueC) (program := #[instrAdd]),
    mkCase "oracle/malformed-root" (mkStack (.cell malformedRoot) 4 key4_2 sampleValueA),
    mkCodeCase "oracle/decode/470" #[] raw470,
    mkCodeCase "oracle/decode/471" #[] raw471,
    mkCodeCase "oracle/decode/472" #[] raw472,
    mkCodeCase "oracle/decode/473" #[] raw473,
    mkCodeCase "oracle/decode/46c" #[] raw46C,
    mkCodeCase "oracle/decode/trunc8" #[] rawF4,
    mkCase "oracle/gas/set-hit-exact"
      (mkStack (.cell pfxRootThree) 4 key4_2 sampleValueA)
      (program := #[instrSet])
      (gasLimits := oracleGasLimitsExact (gasSet .set (some pfxRootThree) key4_2 sampleValueA)),
    mkCase "oracle/gas/set-hit-minus-one"
      (mkStack (.cell pfxRootThree) 4 key4_2 sampleValueA)
      (program := #[instrSet])
      (gasLimits := oracleGasLimitsExactMinusOne (gasSetMinusOne .set (some pfxRootThree) key4_2 sampleValueA)),
    mkCase "oracle/gas/replace-miss-exact"
      (mkStack .null 4 key4_2 sampleValueA)
      (program := #[instrReplace])
      (gasLimits := oracleGasLimitsExact (computeExactGasBudget instrReplace)),
    mkCase "oracle/gas/replace-miss-minus-one"
      (mkStack .null 4 key4_2 sampleValueA)
      (program := #[instrReplace])
      (gasLimits := oracleGasLimitsExactMinusOne
        (if computeExactGasBudget instrReplace > 0 then computeExactGasBudget instrReplace - 1 else 0)),
    mkCase "oracle/gas/add-hit"
      (mkStack (.cell pfxRootTwo23) 4 key4_2 sampleValueA)
      (program := #[instrAdd])
      (gasLimits := oracleGasLimitsExact (computeExactGasBudget instrAdd)),
    mkCase "oracle/gas/add-hit-minus-one"
      (mkStack (.cell pfxRootTwo23) 4 key4_2 sampleValueA)
      (program := #[instrAdd])
      (gasLimits := oracleGasLimitsExactMinusOne
        (if computeExactGasBudget instrAdd > 0 then computeExactGasBudget instrAdd - 1 else 0))
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr pfxDictSetId
      count := 500
      gen := genPFXDICTSET }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTSET
