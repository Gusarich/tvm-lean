import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTGETPREVEQ

/-!
INSTRUCTION: DICTGETPREVEQ

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictDictGetNear` is entered only for `.dictGetNear _`;
     all other opcodes must forward to `next` unchanged.

2. [B2] Runtime underflow path.
   - Exact requirement is 3 stack items: `n` (small-int), `dict` (maybe cell),
     `key_hint` (slice). Any missing item must raise `stkUnd`.

3. [B3] Range/type branch for `n`.
   - For non-int keys (`args4 & 8 = 0`), `n` is validated with
     `popNatUpTo 1023`; negative values and values above 1023 must raise
     `rangeChk`.

4. [B4] Runtime type for dict root.
   - `popMaybeCell` expects a dictionary root slot; a non-cell/non-null
     value is a type error (`typeChk` in Lean / VM error in C++).

5. [B5] Runtime type for key hint.
   - `popSlice` requires third stack item to be a slice; anything else is `typeChk`
     (`popSlice` failure).

6. [B6] Key-hint bit availability.
   - `dictGetPreveq` checks `haveBits n` for the key hint slice.
   - If the slice has fewer than `n` bits, execution raises `cellUnd`.

7. [B7] Lookup miss path.
   - Valid inputs may produce no predecessor match in `dictNearestWithCells`;
     result is a single `0` (false flag) on stack.

8. [B8] Lookup hit path.
   - For a successful predecessor match, `.dictGetNear 7` pushes:
     value slice, reconstructed key slice, then `-1`.
   - Miss/empty behavior for this opcode is direction-aware (`goUp = false`) and
     allows equality (`allowEq = true`).

9. [B9] Dictionary/traversal errors.
   - Malformed roots or traversal failures in `dictNearestWithCells` or visited-set
     loading should raise dictionary errors (`dictErr`/`cellUnd` family).

10. [B10] Assembler encoding/validation.
    - `.dictGetNear args4` is valid only for `4 ≤ args4 ≤ 15`.
    - Any lower/higher `args4` must fail with `.rangeChk`.

11. [B11] Decoder branches.
    - Opcodes `0xF474..0xF47F` decode as `.dictGetNear args4`
      (`args4 = opcode & 0xF`) and consume 16 bits.
    - `0xF480` (next nibble) must be decoding failure (`invOpcode`).
    - Truncated 12-bit stream `0xF47` must fail with `invOpcode`.

12. [B12] Gas accounting.
    - A miss path uses base gas budget.
    - Exact base budget must succeed, while `exact - 1` must fail.
    - Hit path additionally constructs a key slice (`cellCreateGasPrice` branch),
      so base-branch success differs between miss/hit execution.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it exercises.
-/

private def suiteId : InstrId :=
  { name := "DICTGETPREVEQ" }

private def instr : Instr :=
  .dictGetNear 7

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {e}"

private def mkDictSetSliceRoot! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (bits, valueSlice) := entry
      match dictSetSliceWithCells root bits valueSlice .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root after insertion"
      | .error e =>
          panic! s!"{label}: dict set failed with {e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def valueA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD4 8)

private def dict4 : Cell :=
  mkDictSetSliceRoot! "dict4" #[
    (natToBits 8 4, valueA),
    (natToBits 12 4, valueB),
    (natToBits 15 4, valueC)
  ]
private def dict1 : Cell :=
  mkDictSetSliceRoot! "dict1" #[
    (natToBits 1 1, valueD)
  ]
private def dict8 : Cell :=
  mkDictSetSliceRoot! "dict8" #[
    (natToBits 0x2A 8, valueA),
    (natToBits 0x7F 8, valueB),
    (natToBits 0xF0 8, valueC)
  ]
private def dict0 : Cell :=
  mkDictSetSliceRoot! "dict0" #[
    (#[], valueA)
  ]
private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0xF 4) #[]
private def emptySlice : Slice := mkSliceFromBits #[]

private def hint4_0 : Slice := mkSliceFromBits (natToBits 0 4)
private def hint4_2 : Slice := mkSliceFromBits (natToBits 2 4)
private def hint4_4 : Slice := mkSliceFromBits (natToBits 4 4)
private def hint4_8 : Slice := mkSliceFromBits (natToBits 8 4)
private def hint4_10 : Slice := mkSliceFromBits (natToBits 10 4)
private def hint4_12 : Slice := mkSliceFromBits (natToBits 12 4)
private def hint4_14 : Slice := mkSliceFromBits (natToBits 14 4)
private def hint4_15 : Slice := mkSliceFromBits (natToBits 15 4)
private def hint1_0 : Slice := mkSliceFromBits (natToBits 0 1)
private def hint1_1 : Slice := mkSliceFromBits (natToBits 1 1)
private def hint8_0 : Slice := mkSliceFromBits (natToBits 0 8)
private def hint8_1 : Slice := mkSliceFromBits (natToBits 1 8)
private def hint8_42 : Slice := mkSliceFromBits (natToBits 0x2A 8)
private def hint8_127 : Slice := mkSliceFromBits (natToBits 127 8)
private def hint8_42next : Slice := mkSliceFromBits (natToBits 0x2B 8)
private def hint8_80 : Slice := mkSliceFromBits (natToBits 0x80 8)
private def hint8_short : Slice := mkSliceFromBits (natToBits 3 2)
private def hint256bits : Slice :=
  mkSliceFromBits (Array.replicate 257 false)
private def rawOpcodeF474 : Cell := Cell.mkOrdinary (natToBits 0xF474 16) #[]
private def rawOpcodeF47F : Cell := Cell.mkOrdinary (natToBits 0xF47F 16) #[]
private def rawOpcodeF480 : Cell := Cell.mkOrdinary (natToBits 0xF480 16) #[]
private def rawOpcodeF47Trunc : Cell := Cell.mkOrdinary (natToBits 0xF47 12) #[]
private def rawOpcodePair : Cell := Cell.mkOrdinary (natToBits 0xF474 16 ++ natToBits 0xF477 16) #[]

private def dispatchSentinel : Int := 19001

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

private def expectAssembleRangeErr (label : String) (badInstr : Instr) : IO Unit := do
  match assembleCp0 [badInstr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected .rangeChk, got successful assembly")
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .rangeChk, got {e}")

private def runFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetNear .add (VM.push (intV dispatchSentinel)) stack

private def dictGetPreveqGas : Int :=
  computeExactGasBudget instr
private def dictGetPreveqGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr
private def dictGetPreveqGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictGetPreveqGas
private def dictGetPreveqGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExact dictGetPreveqGasMinusOne

private def stackWithHint (hint : Slice) (dict : Value) (n : Int) : Array Value :=
  #[.slice hint, dict, intV n]

private def genDICTGETPREVEQ (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (shapeCase, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/hit/dict4-8" (stackWithHint hint4_8 (.cell dict4) 4), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/hit/dict4-12" (stackWithHint hint4_12 (.cell dict4) 4), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/hit/dict4-15" (stackWithHint hint4_15 (.cell dict4) 4), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/hit/dict4-10-prev" (stackWithHint hint4_10 (.cell dict4) 4), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/hit/dict4-14-prev" (stackWithHint hint4_14 (.cell dict4) 4), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/hit/dict1-1" (stackWithHint hint1_1 (.cell dict1) 1), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/hit/dict8-2a" (stackWithHint hint8_42 (.cell dict8) 8), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/hit/dict8-f0" (stackWithHint hint8_42next (.cell dict8) 8), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/hit/n0-empty" (stackWithHint emptySlice (.cell dict0) 0), rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/miss/before-smallest-dict4" (stackWithHint hint4_4 (.cell dict4) 4), rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/miss/n1-before" (stackWithHint hint1_0 (.cell dict1) 1), rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/miss/empty" (stackWithHint hint4_8 .null 4), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss/maxn-empty"
        (stackWithHint hint256bits (.null) 257),
        rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/range-n-too-large" (stackWithHint hint4_8 (.cell dict4) 1024), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else
      (let (whichGas, rng2') := randBool rng1
       if whichGas then
         (mkCase "fuzz/gas/exact"
            (stackWithHint hint4_8 (.cell dict4) 4)
            #[.pushInt (.num dictGetPreveqGas), .tonEnvOp .setGasLimit, instr]
            dictGetPreveqGasExact,
          rng2')
       else
         (mkCase "fuzz/gas/exact-minus-one"
            (stackWithHint hint4_8 (.cell dict4) 4)
            #[.pushInt (.num dictGetPreveqGasMinusOne), .tonEnvOp .setGasLimit, instr]
            dictGetPreveqGasExactMinusOne,
          rng2'))
  let (tag, rng3) := randNat rng2 0 999_999
  ({ shapeCase with name := s!"{shapeCase.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "unit/dispatch/fallback" (runFallback #[]) #[intV dispatchSentinel] },
    { name := "unit/encoding/assembled-lower-boundary" -- [B10]
      run := do
        let code ←
          match assembleCp0 [instr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"unit/encoding/assembled-lower-boundary: assemble failed: {e}")
        let _ ← expectDecodeStep "unit/decode/assembled" (Slice.ofCell code) (.dictGetNear 7) 16
        let _ ← expectDecodeStep "unit/decode/raw-lower" (Slice.ofCell rawOpcodeF474) (.dictGetNear 4) 16
        let _ ← expectDecodeStep "unit/decode/raw-upper" (Slice.ofCell rawOpcodeF47F) (.dictGetNear 15) 16 },
    { name := "unit/encoding/invalid-args" -- [B10]
      run := do
        expectAssembleRangeErr "unit/encoding/args-too-small" (.dictGetNear 3)
        expectAssembleRangeErr "unit/encoding/args-too-large" (.dictGetNear 16) },
    { name := "unit/decode/invalid-opcode" -- [B11]
      run := do
        let _ ← expectDecodeStep "unit/decode/first-of-pair" (Slice.ofCell rawOpcodePair) (.dictGetNear 4) 16
        match decodeCp0WithBits (Slice.ofCell rawOpcodeF480) with
        | .error _ => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"unit/decode/invalid-opcode: expected failure, got {reprStr instr}, bits={bits}") },
    { name := "unit/decode/truncated" -- [B11]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawOpcodeF47Trunc) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"unit/decode/truncated: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"unit/decode/truncated: expected failure, got {reprStr instr}, bits={bits}") }
  ]
  oracle := #[
    mkCase "ok/hit/dict4-key-8" (stackWithHint hint4_8 (.cell dict4) 4), -- [B8]
    mkCase "ok/hit/dict4-key-12" (stackWithHint hint4_12 (.cell dict4) 4), -- [B8]
    mkCase "ok/hit/dict4-key-15" (stackWithHint hint4_15 (.cell dict4) 4), -- [B8]
    mkCase "ok/hit/dict4-prev-10" (stackWithHint hint4_10 (.cell dict4) 4), -- [B8]
    mkCase "ok/hit/dict4-prev-14" (stackWithHint hint4_14 (.cell dict4) 4), -- [B8]
    mkCase "ok/hit/dict1-key-1" (stackWithHint hint1_1 (.cell dict1) 1), -- [B8]
    mkCase "ok/hit/dict8-key-2A" (stackWithHint hint8_42 (.cell dict8) 8), -- [B8]
    mkCase "ok/hit/dict8-key-42succ" (stackWithHint hint8_42next (.cell dict8) 8), -- [B8]
    mkCase "ok/hit/dict8-key-max" (stackWithHint hint8_80 (.cell dict8) 8), -- [B8]
    mkCase "ok/hit/dict0-key-empty" (stackWithHint emptySlice (.cell dict0) 0), -- [B8]
    mkCase "ok/miss/n4-before-first" (stackWithHint hint4_4 (.cell dict4) 4), -- [B7]
    mkCase "ok/miss/n4-smallest-gap" (stackWithHint hint4_2 (.cell dict4) 4), -- [B7]
    mkCase "ok/miss/n4-empty" (stackWithHint hint4_12 .null 4), -- [B7]
    mkCase "ok/miss/n8-before-first" (stackWithHint hint8_1 (.cell dict8) 8), -- [B7]
    mkCase "ok/miss/n1-before-first" (stackWithHint hint1_0 (.cell dict1) 1), -- [B7]
    mkCase "ok/miss/n8-empty" (stackWithHint hint8_127 .null 8), -- [B7]
    mkCase "ok/miss/n0-empty" (stackWithHint emptySlice .null 0), -- [B7]
    mkCase "ok/miss/n257-empty-zero" (stackWithHint hint256bits .null 257), -- [B7]
    mkCase "err/underflow-empty" #[], -- [B2]
    mkCase "err/underflow-one" #[.slice hint4_8], -- [B2]
    mkCase "err/underflow-two" #[.slice hint4_8, .null], -- [B2]
    mkCase "err/range-n-too-large" (stackWithHint hint4_8 (.cell dict4) 1024), -- [B3]
    mkCase "err/range-n-negative" (stackWithHint hint4_8 (.cell dict4) (-1)), -- [B3]
    mkCase "err/range-n-nan" (#[.slice hint4_8, .cell dict4, .int .nan]), -- [B3]
    mkCase "err/type-dict-not-cell" (stackWithHint hint4_8 (intV 7) 4), -- [B4]
    mkCase "err/type-keyhint-not-slice" (#[.int (.num 7), .cell dict4, intV 4]), -- [B5]
    mkCase "err/keyhint-too-short-n4" (stackWithHint hint8_short (.cell dict4) 4), -- [B6]
    mkCase "err/keyhint-too-short-n8" (stackWithHint hint8_short (.cell dict8) 8), -- [B6]
    mkCase "err/malformed-dict" (stackWithHint hint4_8 (.cell malformedDict) 4), -- [B9]
    mkCase "err/malformed-dict-empty" (stackWithHint hint1_0 (.cell malformedDict) 1), -- [B9]
    mkCase "gas/exact-miss" (stackWithHint hint4_8 .null 4)
      #[.pushInt (.num dictGetPreveqGas), .tonEnvOp .setGasLimit, instr] dictGetPreveqGasExact, -- [B12]
    mkCase "gas/exact-minus-one" (stackWithHint hint4_8 .null 4)
      #[.pushInt (.num dictGetPreveqGasMinusOne), .tonEnvOp .setGasLimit, instr]
      dictGetPreveqGasExactMinusOne, -- [B12]
    mkCase "err/range-n-too-large-highest" (stackWithHint hint4_8 (.cell dict4) 2048), -- [B3]
    mkCase "ok/hit/dict8-edge-127" (stackWithHint hint8_127 (.cell dict8) 8), -- [B8]
    mkCase "ok/miss/n4-short-to-never-hit" (stackWithHint hint4_2 (.cell dict4) 4), -- [B7]
    mkCase "ok/miss/n8-nonzero-short-key" (stackWithHint hint8_0 (.cell dict8) 8), -- [B7]
    mkCase "gas/exact-miss-n8" (stackWithHint hint8_1 .null 8)
      #[.pushInt (.num dictGetPreveqGas), .tonEnvOp .setGasLimit, instr] dictGetPreveqGasExact -- [B12]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTGETPREVEQ }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTGETPREVEQ
