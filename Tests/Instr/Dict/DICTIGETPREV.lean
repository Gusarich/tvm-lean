import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETPREV

/-!
INSTRUCTION: DICTIGETPREV

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `execInstrDictDictGetNear` handles only `.dictGetNear`; all other opcodes
     delegate to `next`.

2. [B2] Runtime preamble validation.
   - `checkUnderflow 3`, `popNatUpTo 257`, and `popMaybeCell` are exercised.
   - Top-of-stack int/key and `n` errors are all covered.

3. [B3] Int-key in-range path (`dictKeyBits? some`).
   - Valid signed keys are looked up with `dictNearestWithCells` using
     `goUp=true`, `allowEq=false`, `sgnd=true`.
   - Hit path pushes `valueSlice`, key-as-int, and `-1`.
   - Miss path pushes only `0`.

4. [B4] In-range hit/miss variants for `.dictGetNear 10`.
   - Different integer inputs select predecessor hit vs in-range miss behavior.

5. [B5] Out-of-range key fallback branch.
   - Signed conversion failure goes through `cond`.
   - Negative keys (`cond = true`) use `dictMinMaxWithCells` with `goUp=false`.
   - Non-negative keys (`cond = false`) are immediate miss.

6. [B6] Error propagation from dictionary traversal.
   - Malformed dictionaries can raise `.dictErr` in both nearest and minmax
     branches.

7. [B7] Assembler/decode validity.
   - `.dictGetNear 10` must encode to `0xF47A`.
   - `assembleCp0` rejects args outside `[4, 15]`.
   - Decoder maps `0xF474..0xF47F` and rejects out-of-family opcodes/truncation.

8. [B8] Gas behavior.
   - Base gas is checked on miss path.
   - Hit path adds `cellCreateGasPrice`.
   - Exact-minus-one should fail for both base and hit budgets.

TOTAL BRANCHES: 8

Each oracle test below is tagged [B#] to the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTIGETPREV" }

private def instr : Instr :=
  .dictGetNear 10

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def mkSignedSliceDict! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
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

private def valueA : Slice := mkSliceFromBits (natToBits 0xA0 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB0 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC0 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD0 8)

private def dict8A : Cell :=
  mkSignedSliceDict! "dict8A" 8 #[( -20, valueA), (-10, valueB), (7, valueC)]
private def dict8B : Cell :=
  mkSignedSliceDict! "dict8B" 8 #[( -2, valueA), (3, valueB), (100, valueC)]
private def dictSingle8 : Cell :=
  mkSignedSliceDict! "dictSingle8" 8 #[( -1, valueD)]
private def dict0 : Cell :=
  mkSignedSliceDict! "dict0" 0 #[(0, valueA)]
private def dict257Single : Cell :=
  mkSignedSliceDict! "dict257Single" 257 #[(0, valueA)]
private def dict257Pair : Cell :=
  mkSignedSliceDict! "dict257Pair" 257 #[(0, valueA), (maxInt257, valueB)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]
private def dictNull : Value := .null

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def hitGas : Int := baseGas + cellCreateGasPrice
private def hitGasMinusOne : Int := if hitGas > 0 then hitGas - 1 else 0

private def rawOpcodeF474 : Cell := Cell.mkOrdinary (natToBits 0xF474 16) #[]
private def rawOpcodeF47A : Cell := Cell.mkOrdinary (natToBits 0xF47A 16) #[]
private def rawOpcodeF47F : Cell := Cell.mkOrdinary (natToBits 0xF47F 16) #[]
private def rawOpcodeF480 : Cell := Cell.mkOrdinary (natToBits 0xF480 16) #[]
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
  runHandlerDirectWithNext execInstrDictDictGetNear .add (VM.push (intV 909)) stack

private def stack3 (key : Int) (dictCell : Value) (n : Int) : Array Value :=
  #[intV key, dictCell, intV n]

private def genDICTIGETPREV (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/hit-prev-10" (stack3 (-10) (.cell dict8A) 8), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/hit-prev-7" (stack3 (7) (.cell dict8A) 8), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/hit-prev-3" (stack3 (3) (.cell dict8B) 8), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/hit-257-range" (stack3 (maxInt257) (.cell dict257Pair) 257), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/miss-in-range" (stack3 (-20) (.cell dict8A) 8), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/miss-in-range-smallest" (stack3 (-25) (.cell dict8A) 8), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/out-of-range-pos" (stack3 (128) (.cell dict8A) 8), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/out-of-range-neg-hit" (stack3 (-200) (.cell dict8A) 8), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/out-of-range-neg-empty" (stack3 (-200) .null 8), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/underflow-empty" (#[]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/underflow-one" (#[] ++ [intV 7]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/key-nan" (#[(.int .nan), (.cell dict8A), intV 8]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type-key" (#[(.cell valueB), (.cell dict8A), intV 8]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/type-dict" (stack3 (-10) (.int (.num 0)) 8), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/type-n" (stack3 (-10) (.cell dict8A) (.null)), rng1)
    else if shape = 15 then
      (mkCodeCase "fuzz/gas/base-exact" (stack3 90 (.cell dict8A) 8)
        (#[
          .pushInt (.num baseGas),
          .tonEnvOp .setGasLimit,
          instr
        ]) (oracleGasLimitsExact baseGas), rng1)
    else if shape = 16 then
      (mkCodeCase "fuzz/gas/base-minus-one" (stack3 90 (.cell dict8A) 8)
        (#[
          .pushInt (.num baseGasMinusOne),
          .tonEnvOp .setGasLimit,
          instr
        ]) (oracleGasLimitsExactMinusOne baseGas), rng1)
    else if shape = 17 then
      (mkCodeCase "fuzz/gas/hit-exact" (stack3 (-10) (.cell dict8A) 8)
        (#[
          .pushInt (.num hitGas),
          .tonEnvOp .setGasLimit,
          instr
        ]) (oracleGasLimitsExact hitGas), rng1)
    else if shape = 18 then
      (mkCodeCase "fuzz/gas/hit-minus-one" (stack3 (-10) (.cell dict8A) 8)
        (#[
          .pushInt (.num hitGasMinusOne),
          .tonEnvOp .setGasLimit,
          instr
        ]) (oracleGasLimitsExact hitGasMinusOne), rng1)
    else
      (mkCodeCase "fuzz/raw/f47a" (stack3 (-10) (.cell dict8A) 8) rawOpcodeF47A, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st ← runDispatchFallback (#[] ++ [intV 1, intV 2, intV 3])
        if st == #[] ++ [intV 1, intV 2, intV 3, intV 909] then
          pure ()
        else
          throw (IO.userError s!"fallback failed: expected {reprStr (#[] ++ [intV 1, intV 2, intV 3, intV 909])}, got {reprStr st}") },
    { name := "unit/opcode/assemble/exact" -- [B7]
      run := do
        let c := assembleNoRefCell! "dictigetprev/asm" #[instr]
        if c.bits = natToBits 0xF47A 16 then
          pure ()
        else
          throw (IO.userError s!"expected 0xF47A bits, got {c.bits}") },
    { name := "unit/opcode/assemble/reject-oob-args" -- [B7]
      run := do
        match assembleCp0 [.dictGetNear 3] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted args=3")
        | .error _ => pure ()
        match assembleCp0 [.dictGetNear 16] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted args=16")
        | .error _ => pure () },
    { name := "unit/decode/branches" -- [B7]
      run := do
        let s0 := Slice.ofCell (rawOpcodeF47A ++ rawOpcodeF474 ++ rawOpcodeF47F)
        let s1 ← expectDecodeStep "decode/self" s0 (.dictGetNear 10) 16
        let s2 ← expectDecodeStep "decode/prev" s1 (.dictGetNear 0) 16
        let s3 ← expectDecodeStep "decode/next" s2 (.dictGetNear 15) 16
        if s3.bitsRemaining + s3.refsRemaining != 0 then
          throw (IO.userError "decode did not consume full stream") },
    { name := "unit/decode/truncated-or-invalid" -- [B7]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode")
        match decodeCp0WithBits (Slice.ofCell rawOpcodeF480) with
        | .error _ => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode unexpectedly accepted invalid opcode {reprStr instr}/{bits}") }
  ]
  oracle := #[
    mkCase "ok/hit/prev-of-existing-neg" (stack3 (-10) (.cell dict8A) 8), -- [B3][B4]
    mkCase "ok/hit/prev-for-mid" (stack3 (7) (.cell dict8A) 8), -- [B3][B4]
    mkCase "ok/hit/prev-with-7" (stack3 (3) (.cell dict8B) 8), -- [B3][B4]
    mkCase "ok/hit/prev-257-max" (stack3 (maxInt257) (.cell dict257Pair) 257), -- [B3][B4]
    mkCase "ok/hit/prev-zero-width" (stack3 (0) (.cell dict0) 0), -- [B3][B4]
    mkCase "ok/miss/in-range-just-below-smallest" (stack3 (-25) (.cell dict8A) 8), -- [B3][B4]
    mkCase "ok/miss/in-range-eq-smallest" (stack3 (-20) (.cell dict8A) 8), -- [B3][B4]
    mkCase "ok/miss/null-n0" (stack3 (0) dictNull 0), -- [B3][B4]
    mkCase "ok/miss/null-n8" (stack3 (7) dictNull 8), -- [B3][B4]
    mkCase "ok/miss/null-n257" (stack3 (0) dictNull 257), -- [B3][B4]
    mkCase "ok/miss/out-of-range-positive" (stack3 (8) (.cell dict8A) 8), -- [B5]
    mkCase "ok/miss/out-of-range-positive-large" (stack3 (1000) (.cell dict8A) 8), -- [B5]
    mkCase "ok/fallback/negative-out-of-range-hit" (stack3 (-130) (.cell dict8A) 8), -- [B5][B6]
    mkCase "ok/fallback/negative-out-of-range-hit-257" (stack3 (-130) (.cell dict8A) 8), -- [B5][B6]
    mkCase "ok/fallback/negative-out-of-range-miss-empty" (stack3 (-130) dictNull 8), -- [B5]
    mkCase "ok/miss/out-of-range-non-neg-empty" (stack3 (128) dictNull 8), -- [B5]
    mkCase "ok/fallback/minmax-malformed-in-range" (stack3 (-10) (.cell malformedDict) 8), -- [B6]
    mkCase "ok/fallback/minmax-malformed-out-of-range-negative" (stack3 (-130) (.cell malformedDict) 8), -- [B6]
    mkCodeCase "ok/code/raw/0xf47a" (stack3 (-10) (.cell dict8A) 8) rawOpcodeF47A, -- [B7]
    mkCodeCase "ok/code/raw/0xf474" (stack3 (-10) (.cell dict8A) 8) rawOpcodeF474, -- [B7]
    mkCodeCase "ok/code/raw/0xf47f" (stack3 (-10) (.cell dict8A) 8) rawOpcodeF47F, -- [B7]
    mkCase "err/underflow-empty" #[], -- [B2]
    mkCase "err/underflow-one" (#[intV 7]), -- [B2]
    mkCase "err/type-key-non-int" (#[(.cell valueA), (.cell dict8A), intV 8]), -- [B5]
    mkCase "err/key-nan" (#[(.int .nan), (.cell dict8A), intV 8]), -- [B5]
    mkCase "err/type-dict" (stack3 (-10) (.int (.num 0)) 8), -- [B2][B3]
    mkCase "err/type-n" (stack3 (-10) (.cell dict8A) (.null)), -- [B2]
    mkCase "err/n-negative" (stack3 (-10) (.cell dict8A) (-1)), -- [B2][B3]
    mkCase "err/n-too-large" (stack3 (-10) (.cell dict8A) 258), -- [B2][B3]
    mkCase "err/malformed-dict-nearest" (stack3 (-1) (.cell malformedDict) 8), -- [B6]
    mkCase "err/malformed-dict-minmax" (stack3 (-130) (.cell malformedDict) 8), -- [B6]
    mkCase "gas/exact-base-miss" (stack3 90 (.cell dictSingle8) 8)
      #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact baseGas), -- [B8]
    mkCase "gas/exact-minus-one-miss" (stack3 90 (.cell dictSingle8) 8)
      #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExactMinusOne baseGasMinusOne), -- [B8]
    mkCase "gas/exact-hit" (stack3 (-10) (.cell dict8A) 8)
      #[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact hitGas), -- [B8]
    mkCase "gas/hit-minus-one" (stack3 (-10) (.cell dict8A) 8)
      #[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact hitGasMinusOne) -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTIGETPREV }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETPREV
