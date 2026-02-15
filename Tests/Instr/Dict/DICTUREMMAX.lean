import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREMMAX

/-!
INSTRUCTION: DICTUREMMAX

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   `.dictGetMinMax` is handled by `execInstrDictDictGetMinMax`; all other opcodes must
   fall through to `next`.

2. [B2] Preamble.
   `checkUnderflow 2` rejects underflow (`.stkUnd`), and `popNatUpTo 256` enforces key width rules,
   rejecting NaN, negative, and >256 inputs (`.rangeChk`).

3. [B3] Root decoding and type handling.
   `popMaybeCell` accepts `.null` and valid dictionary cells, and rejects non-cell/non-null roots
   with `.typeChk`.

4. [B4] Null/non-hit miss path.
   For empty dictionary (`null`) or key-width mismatch in non-empty roots, handler returns only success flag `0`
and preserves original dictionary when present.

5. [B5] Hit path and remove behavior.
   With `remove` set, the handler picks the maximal unsigned key,
   removes it, pushes modified dictionary root, value, key, and success flag `-1`.

6. [B6] Unsigned key-width semantics.
   Valid unsigned widths include `0`, `1`, `2`, `8`, `16`, `128`, and `256`.
   Boundary key behavior (smallest/largest for width) is exercised by selected fixtures.

7. [B7] Dictionary structural errors.
   Malformed dictionary cells raise traversal errors during `dictMinMaxWithCells` / delete pass (`.cellUnd`
   in current fixtures).

8. [B8] Assembler constraints.
   `ExecInstr.dictGetMinMax` accepts disjoint args families including `30` for `DICTUREMMAX`; gap args and
   `>31` are rejected (`.invOpcode` / `.rangeChk`).

9. [B9] Decoder boundaries and aliasing.
   Raw opcodes `0xF49A..0xF49F` decode to arg-family variants (26..31).
   `0xF498`, `0xF490`, and truncated streams reject with decode errors.

10. [B10] Gas accounting, fixed path.
    Exact base gas succeeds for miss path; exact-minus-one base gas fails.

11. [B11] Gas accounting, remove path.
    Remove-hit can add `cellCreateGasPrice` times `created` from `dictDeleteWithCells`; exact budget based
    on fixture-specific `created` succeeds and exact-minus-one fails.

TOTAL BRANCHES: 11
Each oracle test below is tagged [Bn] to its branch coverage.
-/

private def suiteId : InstrId :=
  { name := "DICTUREMMAX" }

private def instr : Instr :=
  .dictGetMinMax 30

private def fallbackSentinel : Int :=
  90_001

private def sampleValueA : Slice :=
  mkSliceFromBits (natToBits 0xA5 8)

private def sampleValueB : Slice :=
  mkSliceFromBits (natToBits 0x5A 8)

private def sampleValueC : Slice :=
  mkSliceFromBits (natToBits 0xC7 8)

private def sampleValueD : Slice :=
  mkSliceFromBits (natToBits 0xD4 8)

private def sampleSlice : Slice :=
  mkSliceFromBits (natToBits 0x55 8)

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid unsigned key={k} for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root for key={k}, n={n}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed for key={k}, n={n}: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: dictionary construction remained empty"

private def dictN0 : Cell := mkDictSetSliceRoot! "DICTUREMMAX/n=0" 0 #[(0, sampleValueA)]
private def dictN1 : Cell := mkDictSetSliceRoot! "DICTUREMMAX/n=1" 1 #[(0, sampleValueA), (1, sampleValueB)]
private def dictN1AfterMax : Cell := mkDictSetSliceRoot! "DICTUREMMAX/n=1-after-max" 1 #[(0, sampleValueA)]

private def dictN2 : Cell := mkDictSetSliceRoot! "DICTUREMMAX/n=2" 2 #[(0, sampleValueA), (3, sampleValueB)]
private def dictN2AfterMax : Cell := mkDictSetSliceRoot! "DICTUREMMAX/n=2-after-max" 2 #[(0, sampleValueA)]

private def dictN8 : Cell :=
  mkDictSetSliceRoot! "DICTUREMMAX/n=8" 8 #[(7, sampleValueA), (127, sampleValueB), (255, sampleValueC)]
private def dictN8AfterMax : Cell :=
  mkDictSetSliceRoot! "DICTUREMMAX/n=8-after-max" 8 #[(7, sampleValueA), (127, sampleValueB)]

private def dictN16 : Cell := mkDictSetSliceRoot! "DICTUREMMAX/n=16" 16 #[(1, sampleValueA), (65535, sampleValueB)]
private def dictN16AfterMax : Cell := mkDictSetSliceRoot! "DICTUREMMAX/n=16-after-max" 16 #[(1, sampleValueA)]

private def dictN256 : Cell :=
  mkDictSetSliceRoot! "DICTUREMMAX/n=256" 256 #[(0, sampleValueA), (3, sampleValueD)]
private def dictN256AfterMax : Cell :=
  mkDictSetSliceRoot! "DICTUREMMAX/n=256-after-max" 256 #[(0, sampleValueA)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def gasBase : OracleGasLimits := oracleGasLimitsExact baseGas
private def gasBaseMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne

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

private def removeN1Created : Nat := dictDeleteCreated dictN1 1
private def removeN2Created : Nat := dictDeleteCreated dictN2 2
private def removeN8Created : Nat := dictDeleteCreated dictN8 8
private def removeN16Created : Nat := dictDeleteCreated dictN16 16
private def removeN256Created : Nat := dictDeleteCreated dictN256 256

private def gasRemoveN1 : Int := baseGas + Int.ofNat removeN1Created * cellCreateGasPrice
private def gasRemoveN1MinusOne : Int := if gasRemoveN1 > 0 then gasRemoveN1 - 1 else 0
private def gasRemoveN2 : Int := baseGas + Int.ofNat removeN2Created * cellCreateGasPrice
private def gasRemoveN2MinusOne : Int := if gasRemoveN2 > 0 then gasRemoveN2 - 1 else 0
private def gasRemoveN8 : Int := baseGas + Int.ofNat removeN8Created * cellCreateGasPrice
private def gasRemoveN8MinusOne : Int := if gasRemoveN8 > 0 then gasRemoveN8 - 1 else 0
private def gasRemoveN16 : Int := baseGas + Int.ofNat removeN16Created * cellCreateGasPrice
private def gasRemoveN16MinusOne : Int := if gasRemoveN16 > 0 then gasRemoveN16 - 1 else 0
private def gasRemoveN256 : Int := baseGas + Int.ofNat removeN256Created * cellCreateGasPrice
private def gasRemoveN256MinusOne : Int := if gasRemoveN256 > 0 then gasRemoveN256 - 1 else 0

private def gasRemoveN1Limits : OracleGasLimits := oracleGasLimitsExact gasRemoveN1
private def gasRemoveN1LimitsMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne gasRemoveN1MinusOne
private def gasRemoveN2Limits : OracleGasLimits := oracleGasLimitsExact gasRemoveN2
private def gasRemoveN2LimitsMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne gasRemoveN2MinusOne
private def gasRemoveN8Limits : OracleGasLimits := oracleGasLimitsExact gasRemoveN8
private def gasRemoveN8LimitsMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne gasRemoveN8MinusOne
private def gasRemoveN16Limits : OracleGasLimits := oracleGasLimitsExact gasRemoveN16
private def gasRemoveN16LimitsMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne gasRemoveN16MinusOne
private def gasRemoveN256Limits : OracleGasLimits := oracleGasLimitsExact gasRemoveN256
private def gasRemoveN256LimitsMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne gasRemoveN256MinusOne

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def rawOpcodeF49A : Cell := raw16 0xF49A
private def rawOpcodeF49B : Cell := raw16 0xF49B
private def rawOpcodeF49C : Cell := raw16 0xF49C
private def rawOpcodeF49D : Cell := raw16 0xF49D
private def rawOpcodeF49E : Cell := raw16 0xF49E
private def rawOpcodeF49F : Cell := raw16 0xF49F
private def rawOpcodeF498 : Cell := raw16 0xF498
private def rawOpcodeF490 : Cell := raw16 0xF490
private def rawTruncated8 : Cell := raw8 0xF4

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

private def mkCaseCode
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
  runHandlerDirectWithNext execInstrDictDictGetMinMax (.add) (VM.push (intV fallbackSentinel)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decode did not consume full stream")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {actual}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr
    (label : String)
    (i : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")

private def expectHitShape
    (label : String)
    (result : Except Excno (Array Value))
    (expectedRoot : Value)
    (expectedKey : Int) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")
  | .ok st =>
      match st with
      | #[root, .slice _, key, flag] =>
          if root != expectedRoot then
            throw (IO.userError s!"{label}: expected root {reprStr expectedRoot}, got {reprStr root}")
          else if key != intV expectedKey then
            throw (IO.userError s!"{label}: expected key {expectedKey}, got {reprStr key}")
          else if flag != intV (-1) then
            throw (IO.userError s!"{label}: expected flag -1, got {reprStr flag}")
      | _ =>
          throw (IO.userError s!"{label}: expected [root, slice, key, -1], got {reprStr st}")

private def genDictURemMaxCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 43
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/hit/n0" (#[.cell dictN0, intV 0]), rng1)
    else if shape = 1 then
      (mkCase "fuzz/hit/n1" (#[.cell dictN1, intV 1]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/hit/n2" (#[.cell dictN2, intV 2]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/hit/n8" (#[.cell dictN8, intV 8]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/n16" (#[.cell dictN16, intV 16]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/n256" (#[.cell dictN256, intV 256]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/miss/null/0" (#[.null, intV 0]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/miss/null/1" (#[.null, intV 1]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/miss/null/16" (#[.null, intV 16]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/miss/null/256" (#[.null, intV 256]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/miss/width-mismatch-short" (#[.cell dictN8, intV 16]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/miss/width-mismatch-long" (#[.cell dictN2, intV 1]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/underflow/empty" (#[] : Array Value), rng1)
    else if shape = 13 then
      (mkCase "fuzz/underflow/one" (#[(intV 8)]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/nan" (#[.null, .int .nan]), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/n-negative" (#[.null, intV (-1)]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/n-overflow" (#[.null, intV 257]), rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/root-slice" (#[.slice sampleSlice, intV 8]), rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/root-tuple" (#[.tuple #[], intV 8]), rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/root-cont" (#[.cont (.quit 0), intV 8]), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/root-malformed" (#[.cell malformedDict, intV 8]), rng1)
    else if shape = 21 then
      (mkCaseCode "fuzz/raw/f49e" (#[.cell dictN8, intV 8]) rawOpcodeF49E, rng1)
    else if shape = 22 then
      (mkCaseCode "fuzz/raw/f49f" (#[.cell dictN8, intV 8]) rawOpcodeF49F, rng1)
    else if shape = 23 then
      (mkCaseCode "fuzz/raw/f49d" (#[.cell dictN8, intV 8]) rawOpcodeF49D, rng1)
    else if shape = 24 then
      (mkCaseCode "fuzz/raw/f49a" (#[.cell dictN8, intV 8]) rawOpcodeF49A, rng1)
    else if shape = 25 then
      (mkCaseCode "fuzz/raw/f498-gap" (#[.cell dictN8, intV 8]) rawOpcodeF498, rng1)
    else if shape = 26 then
      (mkCaseCode "fuzz/raw/f490-gap" (#[.cell dictN8, intV 8]) rawOpcodeF490, rng1)
    else if shape = 27 then
      (mkCaseCode "fuzz/raw/truncated8" #[] rawTruncated8, rng1)
    else if shape = 28 then
      (mkCase "fuzz/gas/base-exact" (#[.null, intV 8])
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) gasBase, rng1)
    else if shape = 29 then
      (mkCase "fuzz/gas/base-minus-one" (#[.null, intV 8])
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]) gasBaseMinusOne, rng1)
    else if shape = 30 then
      (mkCase "fuzz/gas/remove-n1-exact" (#[.cell dictN1, intV 1])
        (#[.pushInt (.num gasRemoveN1), .tonEnvOp .setGasLimit, instr]) gasRemoveN1Limits, rng1)
    else if shape = 31 then
      (mkCase "fuzz/gas/remove-n1-minus-one" (#[.cell dictN1, intV 1])
        (#[.pushInt (.num gasRemoveN1MinusOne), .tonEnvOp .setGasLimit, instr]) gasRemoveN1LimitsMinusOne, rng1)
    else if shape = 32 then
      (mkCase "fuzz/gas/remove-n8-exact" (#[.cell dictN8, intV 8])
        (#[.pushInt (.num gasRemoveN8), .tonEnvOp .setGasLimit, instr]) gasRemoveN8Limits, rng1)
    else if shape = 33 then
      (mkCase "fuzz/gas/remove-n8-minus-one" (#[.cell dictN8, intV 8])
        (#[.pushInt (.num gasRemoveN8MinusOne), .tonEnvOp .setGasLimit, instr]) gasRemoveN8LimitsMinusOne, rng1)
    else if shape = 34 then
      (mkCase "fuzz/gas/remove-n16-exact" (#[.cell dictN16, intV 16])
        (#[.pushInt (.num gasRemoveN16), .tonEnvOp .setGasLimit, instr]) gasRemoveN16Limits, rng1)
    else if shape = 35 then
      (mkCase "fuzz/gas/remove-n16-minus-one" (#[.cell dictN16, intV 16])
        (#[.pushInt (.num gasRemoveN16MinusOne), .tonEnvOp .setGasLimit, instr]) gasRemoveN16LimitsMinusOne, rng1)
    else if shape = 36 then
      (mkCase "fuzz/gas/remove-n256-exact" (#[.cell dictN256, intV 256])
        (#[.pushInt (.num gasRemoveN256), .tonEnvOp .setGasLimit, instr]) gasRemoveN256Limits, rng1)
    else if shape = 37 then
      (mkCase "fuzz/gas/remove-n256-minus-one" (#[.cell dictN256, intV 256])
        (#[.pushInt (.num gasRemoveN256MinusOne), .tonEnvOp .setGasLimit, instr]) gasRemoveN256LimitsMinusOne, rng1)
    else if shape = 38 then
      (mkCase "fuzz/err/wide-hit" (#[.cell dictN8, intV 2]), rng1)
    else if shape = 39 then
      (mkCase "fuzz/err/n-small-overflow" (#[.null, intV (-2)]), rng1)
    else if shape = 40 then
      (mkCase "fuzz/err/wide-miss" (#[.cell dictN16, intV 32]), rng1)
    else if shape = 41 then
      (mkCaseCode "fuzz/raw/f49c" (#[.cell dictN8, intV 8]) rawOpcodeF49C, rng1)
    else if shape = 42 then
      (mkCaseCode "fuzz/raw/f49b" (#[.cell dictN8, intV 8]) rawOpcodeF49B, rng1)
    else
      (mkCase "fuzz/miss/root-malformed-2"
        (#[.cell (Cell.mkOrdinary (natToBits 0xA 3) #[]), intV 8]), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "dispatch/fallback"
          (runDispatchFallback (#[.cell dictN8, intV 8]) )
          #[.cell dictN8, intV 8, intV fallbackSentinel]
    },
    { name := "unit/exec/hit/n0" -- [B2][B3][B5][B6]
      run := do
        expectHitShape "hit/n0" (runDirect (#[.cell dictN0, intV 0])) .null 0
    },
    { name := "unit/exec/hit/n1" -- [B5][B6]
      run := do
        expectHitShape "hit/n1" (runDirect (#[.cell dictN1, intV 1])) (.cell dictN1AfterMax) 1
    },
    { name := "unit/exec/hit/n2" -- [B5][B6]
      run := do
        expectHitShape "hit/n2" (runDirect (#[.cell dictN2, intV 2])) (.cell dictN2AfterMax) 3
    },
    { name := "unit/exec/hit/n8" -- [B5][B6]
      run := do
        expectHitShape "hit/n8" (runDirect (#[.cell dictN8, intV 8])) (.cell dictN8AfterMax) 255
    },
    { name := "unit/exec/hit/n16" -- [B5][B6]
      run := do
        expectHitShape "hit/n16" (runDirect (#[.cell dictN16, intV 16])) (.cell dictN16AfterMax) 65535
    },
    { name := "unit/exec/hit/n256" -- [B5][B6]
      run := do
        expectHitShape "hit/n256" (runDirect (#[.cell dictN256, intV 256])) (.cell dictN256AfterMax) 3
    },
    { name := "unit/exec/miss-null" -- [B4]
      run := do
        expectOkStack "miss/null" (runDirect (#[.null, intV 8])) #[.null, intV 0]
    },
    { name := "unit/exec/miss-width-mismatch-short" -- [B4]
      run := do
        expectHitShape "miss-width-mismatch-short" (runDirect (#[.cell dictN8, intV 16])) (.cell dictN8AfterMax) 65535
    },
    { name := "unit/exec/miss-width-mismatch-long" -- [B4]
      run := do
        expectErr "miss-width-mismatch-long" (runDirect (#[.cell dictN2, intV 64])) .dictErr
    },
    { name := "unit/exec/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect (#[.cell dictN8])) .stkUnd
    },
    { name := "unit/exec/n-errors" -- [B2]
      run := do
        expectErr "nan" (runDirect (#[.null, .int .nan])) .rangeChk
        expectErr "negative" (runDirect (#[.null, intV (-1)]) ) .rangeChk
        expectErr "too-large" (runDirect (#[.null, intV 257])) .rangeChk
    },
    { name := "unit/exec/root-type-errors" -- [B3]
      run := do
        expectErr "root-slice" (runDirect (#[.slice sampleSlice, intV 8])) .typeChk
        expectErr "root-tuple" (runDirect (#[.tuple #[], intV 8])) .typeChk
        expectErr "root-cont" (runDirect (#[.cont (.quit 0), intV 8])) .typeChk
    },
    { name := "unit/exec/malformed-root" -- [B7]
      run := do
        expectErr "malformed-root" (runDirect (#[.cell malformedDict, intV 8])) .cellUnd
    },
    { name := "unit/asm/encode" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xF49E 16 then
              throw (IO.userError "DICTUREMMAX should assemble to 0xF49E")
        | .error e =>
            throw (IO.userError s!"DICTUREMMAX assemble failed: {reprStr e}")
    },
    { name := "unit/asm/reject-gap-and-range" -- [B8]
      run := do
        expectAssembleErr "asm-gap-24" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "asm-range" (.dictGetMinMax 32) .rangeChk
    },
    { name := "unit/decoder/valid" -- [B9]
      run := do
        expectDecodeOk "decode/f49a" rawOpcodeF49A (.dictGetMinMax 26)
        expectDecodeOk "decode/f49e" rawOpcodeF49E (.dictGetMinMax 30)
        expectDecodeOk "decode/f49f" rawOpcodeF49F (.dictGetMinMax 31)
    },
    { name := "unit/decoder/gaps" -- [B9]
      run := do
        expectDecodeErr "decode/f498-gap" rawOpcodeF498 .invOpcode
        expectDecodeErr "decode/f490-gap" rawOpcodeF490 .invOpcode
        expectDecodeErr "decode-truncated" rawTruncated8 .invOpcode
    },
    { name := "unit/exec/gas/exact" -- [B10]
      run := do
        expectHitShape "exact" (runDirect (#[.cell dictN8, intV 8])) (.cell dictN8AfterMax) 255
    }
  ]
  oracle := #[
    mkCase "oracle/hit/n0" (#[.cell dictN0, intV 0]), -- [B5][B6]
    mkCase "oracle/hit/n1" (#[.cell dictN1, intV 1]), -- [B5][B6]
    mkCase "oracle/hit/n2" (#[.cell dictN2, intV 2]), -- [B5][B6]
    mkCase "oracle/hit/n8" (#[.cell dictN8, intV 8]), -- [B5][B6]
    mkCase "oracle/hit/n16" (#[.cell dictN16, intV 16]), -- [B5][B6]
    mkCase "oracle/hit/n256" (#[.cell dictN256, intV 256]), -- [B5][B6]
    mkCase "oracle/miss/null/0" (#[.null, intV 0]), -- [B4]
    mkCase "oracle/miss/null/1" (#[.null, intV 1]), -- [B4]
    mkCase "oracle/miss/null/16" (#[.null, intV 16]), -- [B4]
    mkCase "oracle/miss/null/256" (#[.null, intV 256]), -- [B4]
    mkCase "oracle/miss/short-width" (#[.cell dictN8, intV 16]), -- [B4]
    mkCase "oracle/miss/long-width" (#[.cell dictN2, intV 1]), -- [B4]
    mkCase "oracle/underflow/empty" #[], -- [B2]
    mkCase "oracle/underflow/one-item" (#[intV 8]), -- [B2]
    mkCase "oracle/err/nan" (#[(.null), .int .nan]), -- [B2]
    mkCase "oracle/err/negative" (#[.null, intV (-1)]), -- [B2]
    mkCase "oracle/err/overflow" (#[.null, intV 257]), -- [B2]
    mkCase "oracle/err/root-type-slice" (#[.slice sampleSlice, intV 8]), -- [B3]
    mkCase "oracle/err/root-type-tuple" (#[.tuple #[], intV 8]), -- [B3]
    mkCase "oracle/err/root-type-cont" (#[.cont (.quit 0), intV 8]), -- [B3]
    mkCase "oracle/root-malformed" (#[.cell malformedDict, intV 8]), -- [B7]
    mkCaseCode "oracle/raw/f49a" #[] rawOpcodeF49A, -- [B9]
    mkCaseCode "oracle/raw/f49b" #[] rawOpcodeF49B, -- [B9]
    mkCaseCode "oracle/raw/f49c" #[] rawOpcodeF49C, -- [B9]
    mkCaseCode "oracle/raw/f49d" #[] rawOpcodeF49D, -- [B9]
    mkCaseCode "oracle/raw/f49e" #[] rawOpcodeF49E, -- [B9]
    mkCaseCode "oracle/raw/f49f" #[] rawOpcodeF49F, -- [B9]
    mkCaseCode "oracle/raw/f498-gap" #[] rawOpcodeF498, -- [B9]
    mkCaseCode "oracle/raw/f490-gap" #[] rawOpcodeF490, -- [B9]
    mkCaseCode "oracle/raw/truncated8" #[] rawTruncated8, -- [B9]
    mkCaseCode "oracle/raw/f49c-as-nonRef" (#[.cell dictN8, intV 8]) rawOpcodeF49C, -- [B10]
    mkCase "oracle/asm-gap" (#[.null, intV 8]) (#[.dictGetMinMax 24, .add]) (gasBase), -- [B8]
    mkCase "oracle/gas/base-exact" (#[.null, intV 8])
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) gasBase, -- [B10]
    mkCase "oracle/gas/base-minus-one" (#[.null, intV 8])
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]) gasBaseMinusOne, -- [B10]
    mkCase "oracle/gas/remove-n1" (#[.cell dictN1, intV 1])
      (#[.pushInt (.num gasRemoveN1), .tonEnvOp .setGasLimit, instr]) gasRemoveN1Limits, -- [B11]
    mkCase "oracle/gas/remove-n1-minus-one" (#[.cell dictN1, intV 1])
      (#[.pushInt (.num gasRemoveN1MinusOne), .tonEnvOp .setGasLimit, instr]) gasRemoveN1LimitsMinusOne, -- [B11]
    mkCase "oracle/gas/remove-n2" (#[.cell dictN2, intV 2])
      (#[.pushInt (.num gasRemoveN2), .tonEnvOp .setGasLimit, instr]) gasRemoveN2Limits, -- [B11]
    mkCase "oracle/gas/remove-n2-minus-one" (#[.cell dictN2, intV 2])
      (#[.pushInt (.num gasRemoveN2MinusOne), .tonEnvOp .setGasLimit, instr]) gasRemoveN2LimitsMinusOne, -- [B11]
    mkCase "oracle/gas/remove-n8" (#[.cell dictN8, intV 8])
      (#[.pushInt (.num gasRemoveN8), .tonEnvOp .setGasLimit, instr]) gasRemoveN8Limits, -- [B11]
    mkCase "oracle/gas/remove-n8-minus-one" (#[.cell dictN8, intV 8])
      (#[.pushInt (.num gasRemoveN8MinusOne), .tonEnvOp .setGasLimit, instr]) gasRemoveN8LimitsMinusOne, -- [B11]
    mkCase "oracle/gas/remove-n16" (#[.cell dictN16, intV 16])
      (#[.pushInt (.num gasRemoveN16), .tonEnvOp .setGasLimit, instr]) gasRemoveN16Limits, -- [B11]
    mkCase "oracle/gas/remove-n16-minus-one" (#[.cell dictN16, intV 16])
      (#[.pushInt (.num gasRemoveN16MinusOne), .tonEnvOp .setGasLimit, instr]) gasRemoveN16LimitsMinusOne, -- [B11]
    mkCase "oracle/gas/remove-n256" (#[.cell dictN256, intV 256])
      (#[.pushInt (.num gasRemoveN256), .tonEnvOp .setGasLimit, instr]) gasRemoveN256Limits, -- [B11]
    { name := "oracle/gas/remove-n256-minus-one" -- [B11]
      instr := suiteId
      program := #[.pushInt (.num gasRemoveN256MinusOne), .tonEnvOp .setGasLimit, instr]
      initStack := #[.cell dictN256, intV 256]
      gasLimits := gasRemoveN256LimitsMinusOne
      fuel := 1_000_000
    }
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictURemMaxCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREMMAX
