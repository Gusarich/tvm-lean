import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETNEXT

/-!
INSTRUCTION: DICTIGETNEXT

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch:
   - `execInstrDictDictGetNear` handles `.dictGetNear args4` and forwards other opcodes to `next`.

2. [B2] Runtime preamble/validation:
   - `checkUnderflow 3`, `popNatUpTo 257`, `popMaybeCell`, and `popIntFinite` are all required.
   - Stack/type/range failures for these inputs produce standard runtime exceptions.

3. [B3] Signed in-range key path:
   - For representable key (`dictKeyBits?` returns `some`), execution uses
     `dictNearestWithCells` with `goUp=true`, `allowEq=false`, `sgnd=true`.
   - Hit path pushes `[valueSlice, keyInt, -1]`.
   - Miss path pushes `[0]`.

4. [B4] Out-of-range negative key path:
   - `dictKeyBits?` returns `none` and `cond` is true for negative keys.
   - Execution uses `dictMinMaxWithCells` with `fetchMax = true` (`min` endpoint in TVM terms) to emulate NEXT lower-bound fallback.
   - Non-empty dictionaries can still hit; empty dict gives `[0]`.

5. [B5] Out-of-range non-negative key path:
   - `cond` is false for non-negative keys, so execution returns `[0]` without dictionary lookup.

6. [B6] Dictionary structural errors:
   - Malformed dictionary roots can fail in both nearest (`dictNearestVisitedCells`) and min/max (`dictMinMaxVisitedCells`) branches.

7. [B7] Assembler/decoder behavior:
   - `.dictGetNear 8` must assemble to `0xF478`.
   - `assembleCp0` rejects args outside `[4,15]`.
   - Decoder maps `0xF474..0xF47F`; `0xF480` and truncated prefixes are rejected.

8. [B8] Gas accounting:
   - Base gas is fixed for this instruction and tested with exact and exact-1.
   - No extra `cellCreateGasPrice` branch exists for integer-key mode.

TOTAL BRANCHES: 8

Runtime, decoder, and gas categories are all explicitly covered by oracle tests; remaining branches are
exercised by the fuzzer and targeted raw-code oracle entries.
-/

private def suiteId : InstrId :=
  { name := "DICTIGETNEXT" }

private def instr : Instr :=
  .dictGetNear 8

private def dispatchSentinel : Int :=
  9077

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def mkSignedDict (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: key out of range ({k}, n={n})"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) => root := r
      | .ok (none, _, _, _) => panic! s!"{label}: unexpected empty root"
      | .error e => panic! s!"{label}: dict insert failed ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict"

private def valueA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xE5 8)
private def valueF : Slice := mkSliceFromBits (natToBits 0xF6 8)

private def dict8A : Value :=
  .cell <| mkSignedDict "dict8A" 8 #[
    (-128, valueA), (-1, valueB), (5, valueC), (90, valueD), (127, valueE)
  ]

private def dict8B : Value :=
  .cell <| mkSignedDict "dict8B" 8 #[
    (-50, valueF), (3, valueA), (9, valueB)
  ]

private def dict257A : Value :=
  .cell <| mkSignedDict "dict257A" 257 #[
    (0, valueC), (1, valueD), (maxInt257, valueE)
  ]

private def dictNull : Value := .null

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def exactGas : Int :=
  computeExactGasBudget instr

private def exactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def rawF478 : Cell := Cell.mkOrdinary (natToBits 0xF478 16) #[]
private def rawF47A : Cell := Cell.mkOrdinary (natToBits 0xF47A 16) #[]
private def rawF47F : Cell := Cell.mkOrdinary (natToBits 0xF47F 16) #[]
private def rawF47B : Cell := Cell.mkOrdinary (natToBits 0xF47B 16) #[]
private def rawF479 : Cell := Cell.mkOrdinary (natToBits 0xF479 16) #[]
private def rawF480 : Cell := Cell.mkOrdinary (natToBits 0xF480 16) #[]
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

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetNear .add (VM.push (intV dispatchSentinel)) stack

private def runDirect : Array Value → Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetNear instr

private def stack3 (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[intV key, dict, intV n]

private def addSuffix (name : String) (rng0 : StdGen) : String × StdGen :=
  let (x, rng1) := randNat rng0 0 999_999
  (s!"{name}/{x}", rng1)

private def genDICTIGETNEXT (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/hit/neg-bound" (stack3 (-128) dict8A 8), rng1) -- [B3]
    else if shape = 1 then
      (mkCase "fuzz/hit/mid-1" (stack3 (-1) dict8A 8), rng1) -- [B3]
    else if shape = 2 then
      (mkCase "fuzz/hit/127-gap" (stack3 126 dict8A 8), rng1) -- [B3]
    else if shape = 3 then
      (mkCase "fuzz/hit/edge-257" (stack3 (-1) dict257A 257), rng1) -- [B3]
    else if shape = 4 then
      (mkCase "fuzz/miss/upperbound-hitless" (stack3 127 dict8A 8), rng1) -- [B3][B5]
    else if shape = 5 then
      (mkCase "fuzz/miss/in-empty" (stack3 7 dictNull 8), rng1) -- [B3]
    else if shape = 6 then
      (mkCase "fuzz/oob-pos/128" (stack3 128 dict8A 8), rng1) -- [B5]
    else if shape = 7 then
      (mkCase "fuzz/oob-pos/huge" (stack3 1_000 dict8A 8), rng1) -- [B5]
    else if shape = 8 then
      (mkCase "fuzz/oob-neg/fallback-hit" (stack3 (-129) dict8A 8), rng1) -- [B4]
    else if shape = 9 then
      (mkCase "fuzz/oob-neg/empty" (stack3 (-129) dictNull 8), rng1) -- [B4]
    else if shape = 10 then
      (mkCase "fuzz/oob-neg/minInt257" (stack3 minInt257 dict8A 8), rng1) -- [B4]
    else if shape = 11 then
      (mkCase "fuzz/oob-pos/maxInt257" (stack3 maxInt257 dict8A 8), rng1) -- [B5]
    else if shape = 12 then
      (mkCase "fuzz/underflow/empty" #[], rng1) -- [B2]
    else if shape = 13 then
      (mkCase "fuzz/underflow/one" #[intV 7], rng1) -- [B2]
    else if shape = 14 then
      (mkCase "fuzz/underflow/two" (stack3 5 dict8A 8 |>.take 2), rng1) -- [B2]
    else if shape = 15 then
      (mkCase "fuzz/type/n-bad" (#[(intV 5), dict8A, .tuple #[]]), rng1) -- [B2]
    else if shape = 16 then
      (mkCase "fuzz/type/key-non-int" (#[.tuple #[], dict8A, intV 8]), rng1) -- [B2]
    else if shape = 17 then
      (mkCase "fuzz/type/key-nan"
        (#[dict8A, intV 8])
        #[.pushInt .nan, .xchg0 1, .xchg 1 2, instr], rng1) -- [B2]
    else if shape = 18 then
      (mkCase "fuzz/type/dict" (stack3 5 (.int (.num 0)) 8), rng1) -- [B2]
    else if shape = 19 then
      (mkCase "fuzz/type/n-negative" (stack3 5 dict8A (-1)), rng1) -- [B2]
    else if shape = 20 then
      (mkCase "fuzz/malformed/nearest" (stack3 5 (.cell malformedDict) 8), rng1) -- [B6]
    else if shape = 21 then
      (mkCodeCase "fuzz/raw/f478" (stack3 5 dict8A 8) rawF478, rng1) -- [B7]
    else
      (mkCodeCase "fuzz/raw/trunc8" #[] rawTruncated8, rng1) -- [B7]
  let (name, rng3) := addSuffix case0.name rng2
  ({ case0 with name := name }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := stack3 7 dict8A 8
        let expected := stack.push (intV dispatchSentinel)
        expectOkStack "dispatch/fallback" (runDispatchFallback stack) expected },
    { name := "unit/assemble/exact" -- [B7]
      run := do
        let c := assembleNoRefCell! "dictigetnext/asm" #[instr]
        if c.bits = natToBits 0xF478 16 then
          pure ()
        else
          throw (IO.userError s!"expected 0xF478 bits, got {c.bits}") },
    { name := "unit/assemble/reject-low-args" -- [B7]
      run := do
        match assembleCp0 [Instr.dictGetNear 3] with
        | .ok _ => throw (IO.userError "assemble accepted args4=3, expected rangeChk")
        | .error _ => pure () },
    { name := "unit/assemble/reject-high-args" -- [B7]
      run := do
        match assembleCp0 [Instr.dictGetNear 16] with
        | .ok _ => throw (IO.userError "assemble accepted args4=16, expected rangeChk")
        | .error _ => pure () },
    { name := "unit/direct/hit/-128" -- [B3]
      run := do
        match runDirect (stack3 (-128) dict8A 8) with
        | .ok #[.slice _, .int (.num (-1)), .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"direct/hit/min: expected [slice,-1,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"direct/hit/min: expected success, got {e}") },
    { name := "unit/direct/hit/5" -- [B3]
      run := do
        match runDirect (stack3 5 dict8A 8) with
        | .ok #[.slice _, .int (.num 90), .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"direct/hit/between: expected [slice,90,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"direct/hit/between: expected success, got {e}") },
    { name := "unit/direct/hit/126" -- [B3]
      run := do
        match runDirect (stack3 126 dict8A 8) with
        | .ok #[.slice _, .int (.num 127), .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"direct/hit/next-126: expected [slice,127,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"direct/hit/next-126: expected success, got {e}") },
    { name := "unit/direct/miss/at-upperbound" -- [B3][B5]
      run := do
        expectOkStack "direct/miss/top" (runDirect (stack3 127 dict8A 8))
          #[intV 0] },
    { name := "unit/direct/miss/empty" -- [B3]
      run := do
        expectOkStack "direct/miss/empty" (runDirect (stack3 7 dictNull 8))
          #[intV 0] },
    { name := "unit/direct/miss/oob-positive" -- [B5]
      run := do
        expectOkStack "direct/miss/oob-positive" (runDirect (stack3 129 dict8A 8))
          #[intV 0] },
    { name := "unit/direct/fallback/oob-negative" -- [B4]
      run := do
        match runDirect (stack3 (-129) dict8A 8) with
        | .ok #[.slice _, .int (.num (-128)), .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"direct/fallback/oob-negative: expected [slice,-128,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"direct/fallback/oob-negative: expected success, got {e}") },
    { name := "unit/direct/fallback/oob-negative-empty" -- [B4]
      run := do
        expectOkStack "direct/fallback/oob-negative-empty" (runDirect (stack3 (-129) dictNull 8))
          #[intV 0] },
    { name := "unit/direct/err/malformed-nearest" -- [B6]
      run := do
        match runDirect (stack3 7 (.cell malformedDict) 8) with
        | .error .dictErr => pure ()
        | .error .cellUnd => pure ()
        | .error e =>
            throw (IO.userError s!"direct/malformed-nearest: expected dictErr/cellUnd, got {e}")
        | .ok st =>
            throw (IO.userError s!"direct/malformed-nearest: expected failure, got {reprStr st}") },
    { name := "unit/direct/err/malformed-minmax" -- [B6]
      run := do
        match runDirect (stack3 (-129) (.cell malformedDict) 8) with
        | .error .dictErr => pure ()
        | .error .cellUnd => pure ()
        | .error e =>
            throw (IO.userError s!"direct/malformed-minmax: expected dictErr/cellUnd, got {e}")
        | .ok st =>
            throw (IO.userError s!"direct/malformed-minmax: expected failure, got {reprStr st}") },
    { name := "unit/decode/chain-and-boundary" -- [B7]
      run := do
        let s0 :=
          Slice.ofCell <| Cell.mkOrdinary
            (rawF478.bits ++ rawF479.bits ++ rawF47A.bits ++ rawF47B.bits ++ rawF47F.bits) #[]
        let s1 ← expectDecodeStep "decode/f478" s0 (.dictGetNear 8) 16
        let s2 ← expectDecodeStep "decode/f479" s1 (.dictGetNear 9) 16
        let s3 ← expectDecodeStep "decode/f47a" s2 (.dictGetNear 10) 16
        let s4 ← expectDecodeStep "decode/f47b" s3 (.dictGetNear 11) 16
        let s5 ← expectDecodeStep "decode/f47f" s4 (.dictGetNear 15) 16
        if s5.bitsRemaining + s5.refsRemaining != 0 then
          throw (IO.userError "decode chain did not consume stream")
        match decodeCp0WithBits (Slice.ofCell rawF480) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted 0xF480") },
    { name := "unit/decode/truncated" -- [B7]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode") }
  ]
  oracle := #[
    mkCase "ok/hit/negative-128" (stack3 (-128) dict8A 8), -- [B3]
    mkCase "ok/hit/negative-1" (stack3 (-1) dict8A 8), -- [B3]
    mkCase "ok/hit/4" (stack3 4 dict8A 8), -- [B3]
    mkCase "ok/hit/6" (stack3 6 dict8A 8), -- [B3]
    mkCase "ok/hit/10" (stack3 10 dict8A 8), -- [B3]
    mkCase "ok/hit/126" (stack3 126 dict8A 8), -- [B3]
    mkCase "ok/hit/257-minus-one" (stack3 (-1) dict257A 257), -- [B3]
    mkCase "ok/miss/upperbound" (stack3 127 dict8A 8), -- [B3]
    mkCase "ok/miss/empty" (stack3 42 dictNull 8), -- [B3]
    mkCase "ok/miss/empty-257" (stack3 42 dictNull 257), -- [B3]
    mkCase "ok/oob-pos-128" (stack3 128 dict8A 8), -- [B5]
    mkCase "ok/oob-pos-large" (stack3 1_000_000 dict8A 8), -- [B5]
    mkCase "ok/oob-pos-maxInt257" (stack3 maxInt257 dict8A 8), -- [B5]
    mkCase "ok/oob-neg" (stack3 (-129) dict8A 8), -- [B4]
    mkCase "ok/oob-neg-empty" (stack3 (-129) dictNull 8), -- [B4]
    mkCase "ok/oob-neg-minInt257" (stack3 minInt257 dict8A 8), -- [B4]
    mkCase "ok/oob-neg-minInt257-empty" (stack3 minInt257 dictNull 8), -- [B4]
    mkCase "err/underflow-empty" #[], -- [B2]
    mkCase "err/underflow-one" #[intV 7], -- [B2]
    mkCase "err/underflow-two" (stack3 5 dict8A 8 |>.take 2), -- [B2]
    mkCase "err/n/type" (#[.int (.num 5), dict8A, .tuple #[]]), -- [B2]
    mkCase "err/n/nan"
      (#[intV 5, dict8A])
      #[.pushInt .nan, instr], -- [B2]
    mkCase "err/n/negative" (stack3 5 dict8A (-1)), -- [B2]
    mkCase "err/n/too-large" (stack3 5 dict8A 258), -- [B2]
    mkCase "err/key/type" (#[.tuple #[], dict8A, intV 8]), -- [B2]
    mkCase "err/key/nan"
      (#[dict8A, intV 8])
      #[.pushInt .nan, .xchg0 1, .xchg 1 2, instr], -- [B2]
    mkCase "err/dict/type" (stack3 5 (.int (.num 0)) 8), -- [B2]
    mkCase "err/malformed/dict-nearest" (stack3 5 (.cell malformedDict) 8), -- [B6]
    mkCase "err/malformed/dict-minmax" (stack3 (-129) (.cell malformedDict) 8), -- [B6]
    mkCodeCase "ok/code/f47f" (stack3 7 dict8A 8) rawF47F, -- [B7]
    mkCodeCase "ok/code/f47a" (stack3 7 dict8A 8) rawF47A, -- [B7]
    mkCodeCase "ok/code/f478" (stack3 7 dict8A 8) rawF478, -- [B7]
    mkCodeCase "err/code/truncated" (#[] ) rawTruncated8, -- [B7]
    mkCase "gas/exact-success" (stack3 7 dict8A 8)
      #[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact exactGas), -- [B8]
    mkCase "gas/exact-minus-one" (stack3 7 dict8A 8)
      #[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExactMinusOne exactGasMinusOne), -- [B8]
    mkCase "gas/exact-success-257" (stack3 (-1) dict257A 257)
      #[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact exactGas), -- [B8]
    mkCase "gas/exact-minus-one-257" (stack3 (-1) dict257A 257)
      #[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExactMinusOne exactGasMinusOne) -- [B8]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 500
      gen := genDICTIGETNEXT }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETNEXT
