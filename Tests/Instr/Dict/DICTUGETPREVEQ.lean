import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETPREVEQ

/-
INSTRUCTION: DICTUGETPREVEQ

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatcher path.
   - `execInstrDictDictGetNear` must handle `.dictGetNear` instructions.
   - All other opcodes must delegate to `next`.

2. [B2] Runtime preamble and stack shape validation.
   - `checkUnderflow 3` must enforce all three operands are present.
   - `popNatUpTo 256` must reject negative/out-of-range `n`.
   - `popMaybeCell` enforces dictionary root shape, while
     `popIntFinite` enforces key type and finiteness.

3. [B3] Unsigned representability checks (`dictKeyBits?` + bounds).
   - `0 <= key < 2^n` must convert to key bits successfully.
   - Negative keys, non-finite keys, and oversized keys must hit representability failure paths.

4. [B4] Signed-keyless representable-hit path.
   - For representable unsigned keys, `dictNearestWithCells` is used.
   - Hit pushes `value`, integer key, and `-1`.

5. [B5] Representable-miss path.
   - `dictNearestWithCells` may return none and push only `0`.

6. [B6] Out-of-range negative key path.
   - Since `goUp = false` for PREV and `cond = (0 ≤ key) != false`, negative keys must
     bypass `dictMinMaxWithCells` and return immediate miss (`0`).

7. [B7] Out-of-range non-negative key fallback path.
   - Non-negative keys that are not representable must invoke `dictMinMaxWithCells`.
   - Fallback can hit (returns max key) or miss when root is empty.

8. [B8] Dictionary traversal errors.
   - Malformed root in `dictNearestWithCells` must return an error.
   - Malformed root in fallback `dictMinMaxWithCells` must return an error.

9. [B9] Assembler validation.
   - `.dictGetNear` rejects `args4 < 4` and `args4 > 15`.
   - `.dictGetNear 15` must assemble to `0xF47F`.

10. [B10] Decoder validation.
   - Decoder accepts `0xF474..0xF47F` in fixed range and maps
     each nibble to `.dictGetNear args4`.
   - Adjacent opcode (`0xF480`) and truncated slice (`0xF47`) must fail decode.

11. [B11] Gas accounting.
   - Base gas is consumed for both miss and hit paths in unsigned mode.
   - `computeExactGasBudget` and `exact-1` must differ in success/failure behavior.
   - No additional variable hit surcharge in this int-key branch (cell key reconstruction is not used).

TOTAL BRANCHES: 11

Each oracle test below is tagged [B#] to the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTUGETPREVEQ" }

private def dictUGetPrevEqInstr : Instr := .dictGetNear 15

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def mkUnsignedDict! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid unsigned key ({k}, n={n})"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary after insertions"

private def valueA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB1 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC1 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD1 8)

private def dict8A : Cell :=
  mkUnsignedDict! "dict8A" 8 #[(0, valueA), (5, valueB), (20, valueC)]

private def dict8Gap : Cell :=
  mkUnsignedDict! "dict8Gap" 8 #[(10, valueA), (20, valueB)]

private def dict1 : Cell :=
  mkUnsignedDict! "dict1" 1 #[(0, valueA), (1, valueB)]

private def dict0 : Cell :=
  mkUnsignedDict! "dict0" 0 #[(0, valueC)]

private def dict8Single : Cell :=
  mkUnsignedDict! "dict8Single" 8 #[(200, valueD)]

private def dictU256Max : Cell :=
  mkUnsignedDict! "dictU256Max" 256 #[(maxUnsignedByBytes 32, valueA)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1111 4) #[]

private def dictUGetPrevEqGas : Int :=
  computeExactGasBudget dictUGetPrevEqInstr

private def dictUGetPrevEqGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictUGetPrevEqInstr

private def rawF474 : Cell := Cell.mkOrdinary (natToBits 0xF474 16) #[]
private def rawF47E : Cell := Cell.mkOrdinary (natToBits 0xF47E 16) #[]
private def rawF47F : Cell := Cell.mkOrdinary (natToBits 0xF47F 16) #[]
private def rawF480 : Cell := Cell.mkOrdinary (natToBits 0xF480 16) #[]
private def rawF47Trunc : Cell := Cell.mkOrdinary (natToBits 0xF47 12) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictUGetPrevEqInstr])
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

private def expectAssembleRangeErr (label : String) (badInstr : Instr) : IO Unit := do
  match assembleCp0 [badInstr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected .rangeChk, got success")
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .rangeChk, got {reprStr e}")

private def stack3 (key : Int) (dictCell : Value) (n : Int) : Array Value :=
  #[intV key, dictCell, intV n]

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetNear .add (VM.push (intV 909)) stack

private def genDICTUGETPREVEQ (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/hit/n0-zero" (stack3 0 (.cell dict0) 0), rng1)
    else if shape = 1 then
      (mkCase "fuzz/hit/n1-key0" (stack3 0 (.cell dict1) 1), rng1)
    else if shape = 2 then
      (mkCase "fuzz/hit/n1-key1" (stack3 1 (.cell dict1) 1), rng1)
    else if shape = 3 then
      (mkCase "fuzz/hit/n8-mid" (stack3 5 (.cell dict8A) 8), rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/n8-max" (stack3 200 (.cell dict8A) 8), rng1)
    else if shape = 5 then
      (mkCase "fuzz/miss/in-range-gap" (stack3 5 (.cell dict8Gap) 8), rng1)
    else if shape = 6 then
      (mkCase "fuzz/miss/in-range-empty" (stack3 5 .null 8), rng1)
    else if shape = 7 then
      (mkCase "fuzz/neg-miss-immediate" (stack3 (-1) (.cell dict8A) 8), rng1)
    else if shape = 8 then
      (mkCase "fuzz/neg-miss-empty" (stack3 (-1) .null 8), rng1)
    else if shape = 9 then
      (mkCase "fuzz/fallback/n8-hit-256" (stack3 256 (.cell dict8Gap) 8), rng1)
    else if shape = 10 then
      (mkCase "fuzz/fallback/n8-hit-300" (stack3 300 (.cell dict8Gap) 8), rng1)
    else if shape = 11 then
      (mkCase "fuzz/fallback/n8-empty" (stack3 255 .null 8), rng1)
    else if shape = 12 then
      (mkCase "fuzz/fallback/n1-hit" (stack3 2 (.cell dict1) 1), rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/nearest-malformed" (stack3 5 (.cell malformedDict) 8), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/minmax-malformed" (stack3 256 (.cell malformedDict) 8), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/underflow-one" #[.int (.num 7)], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/underflow-two" #[.int (.num 7), .null], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/n-negative" (stack3 1 (.cell dict8A) (-1)), rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/n-out-of-range" (stack3 1 (.cell dict8A) 257), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/n-non-int" (#[.cell dict8A, intV 1, .null]), rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/key-type" (#[.slice valueA, .cell dict8A, intV 8]), rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/key-nan" (#[.int .nan, .cell dict8A, intV 8]), rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/exact-hit" (stack3 200 (.cell dict8A) 8)
        (#[
          .pushInt (.num dictUGetPrevEqGas),
          .tonEnvOp .setGasLimit,
          dictUGetPrevEqInstr
        ]) (oracleGasLimitsExact dictUGetPrevEqGas), rng1)
    else
      (mkCase "fuzz/gas/exact-minus-one" (stack3 200 (.cell dict8A) 8)
        (#[
          .pushInt (.num dictUGetPrevEqGasMinusOne),
          .tonEnvOp .setGasLimit,
          dictUGetPrevEqInstr
        ]) (oracleGasLimitsExact dictUGetPrevEqGasMinusOne), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDispatchFallback #[] with
        | .ok st =>
            if st == #[intV 909] then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback: expected {[intV 909]}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback failed with {e}")
    }
    ,
    { name := "unit/encode/exact" -- [B9]
      run := do
        let code := assembleNoRefCell! "dictugetpreveq/asm" #[dictUGetPrevEqInstr]
        if code.bits = natToBits 0xF47F 16 then
          pure ()
        else
          throw (IO.userError s!"unit/encode/exact: expected 0xF47F, got {code.bits}")
    }
    ,
    { name := "unit/encode/reject-lower-args4" -- [B9]
      run := do
        expectAssembleRangeErr "unit/encode/reject-lower-args4" (.dictGetNear 3)
    }
    ,
    { name := "unit/encode/reject-upper-args4" -- [B9]
      run := do
        expectAssembleRangeErr "unit/encode/reject-upper-args4" (.dictGetNear 16)
    }
    ,
    { name := "unit/decode/family" -- [B10]
      run := do
        let packed := Cell.mkOrdinary (rawF474.bits ++ rawF47E.bits ++ rawF47F.bits) #[]
        let s0 := Slice.ofCell packed
        let s1 ← expectDecodeStep "decode/F474" s0 (.dictGetNear 4) 16
        let s2 ← expectDecodeStep "decode/F47E" s1 (.dictGetNear 14) 16
        let _ ← expectDecodeStep "decode/F47F" s2 (.dictGetNear 15) 16
        pure ()
    }
    ,
    { name := "unit/decode/invalid" -- [B10]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawF480) with
        | .error _ => pure ()
        | .ok (i, _, _) =>
            throw (IO.userError s!"unit/decode/invalid expected failure, got {reprStr i}")
        match decodeCp0WithBits (Slice.ofCell rawF47Trunc) with
        | .error _ => pure ()
        | .ok (i, _, _) =>
            throw (IO.userError s!"unit/decode/truncated expected failure, got {reprStr i}")
    }
  ]
  oracle := #[
    mkCase "ok/hit/n0-zero" (stack3 0 (.cell dict0) 0), -- [B2] [B3] [B4]
    mkCase "ok/hit/n1-key0" (stack3 0 (.cell dict1) 1), -- [B2] [B3] [B4]
    mkCase "ok/hit/n1-key1" (stack3 1 (.cell dict1) 1), -- [B2] [B3] [B4]
    mkCase "ok/hit/n8-mid" (stack3 5 (.cell dict8A) 8), -- [B3] [B4]
    mkCase "ok/hit/n8-max-edge" (stack3 200 (.cell dict8A) 8), -- [B3] [B4]
    mkCase "ok/hit/n8-single" (stack3 200 (.cell dict8Single) 8), -- [B4]
    mkCase "ok/hit/n256-boundary" (stack3 (maxUnsignedByBytes 32) (.cell dictU256Max) 256), -- [B3] [B4]
    mkCase "ok/miss/in-range-gap" (stack3 15 (.cell dict8Gap) 8), -- [B3] [B5]
    mkCase "ok/miss/n8-empty" (stack3 15 .null 8), -- [B2] [B5]
    mkCase "ok/miss/n1" (stack3 0 (.cell dict1) 1), -- [B5]
    mkCase "ok/miss/negative-immediate" (stack3 (-1) (.cell dict8A) 8), -- [B6]
    mkCase "ok/miss/negative-empty" (stack3 (-1) .null 8), -- [B6]
    mkCase "ok/fallback/hit-n8" (stack3 300 (.cell dict8A) 8), -- [B7]
    mkCase "ok/fallback/hit-n8-low" (stack3 255 (.cell dict8A) 8), -- [B7]
    mkCase "ok/fallback/n1-hit" (stack3 2 (.cell dict1) 1), -- [B7]
    mkCase "ok/fallback/n8-empty-miss" (stack3 255 .null 8), -- [B7]
    mkCase "err/underflow-empty" #[], -- [B2]
    mkCase "err/underflow-one" #[.int (.num 1)], -- [B2]
    mkCase "err/underflow-two" #[.int (.num 1), .null], -- [B2]
    mkCase "err/n-negative" (stack3 1 (.cell dict8A) (-1)), -- [B2] [B3]
    mkCase "err/n-too-large" (stack3 1 (.cell dict8A) 257), -- [B2] [B3]
    mkCase "err/n-non-int" (#[.cell dict8A, intV 1, .null]), -- [B2]
    mkCase "err/key-type" (#[.null, .cell dict8A, intV 8]), -- [B2]
    mkCase "err/key-nan" (#[.int .nan, .cell dict8A, intV 8]), -- [B2]
    mkCase "err/dict-type" (stack3 1 (.int (.num 7)) 8), -- [B2]
    mkCase "err/malformed-nearest" (stack3 5 (.cell malformedDict) 8), -- [B8]
    mkCase "err/malformed-minmax" (stack3 200 (.cell malformedDict) 8), -- [B8]
    mkCodeCase "ok/raw/f47f" (stack3 5 (.cell dict8A) 8) rawF47F, -- [B10]
    mkCodeCase "ok/raw/f47e" (stack3 5 (.cell dict8A) 8) rawF47E, -- [B10]
    mkCodeCase "ok/raw/f474" (stack3 5 (.cell dict8A) 8) rawF474, -- [B10]
    mkCodeCase "err/raw/f47f-misread" (stack3 5 (.cell dict8A) 8) rawF480, -- [B10]
    mkCodeCase "err/raw/f47-trunc" (stack3 5 (.cell dict8A) 8) rawF47Trunc, -- [B10]
    mkCase "gas/exact" (stack3 200 (.cell dict8A) 8)
      (#[.pushInt (.num dictUGetPrevEqGas), .tonEnvOp .setGasLimit, dictUGetPrevEqInstr])
      (oracleGasLimitsExact dictUGetPrevEqGas), -- [B11]
    mkCase "gas/exact-minus-one" (stack3 200 (.cell dict8A) 8)
      (#[.pushInt (.num dictUGetPrevEqGasMinusOne), .tonEnvOp .setGasLimit, dictUGetPrevEqInstr])
      (oracleGasLimitsExact dictUGetPrevEqGasMinusOne) -- [B11]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTUGETPREVEQ }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETPREVEQ
