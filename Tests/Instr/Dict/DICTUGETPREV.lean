import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETPREV

/-!
INSTRUCTION: DICTUGETPREV

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `execInstrDictDictGetNear` handles `.dictGetNear` and dispatches all other opcodes to `next`.

2. [B2] Runtime preamble/validation.
   - Stack underflow/stack shape checks (`checkUnderflow 3`) must be exercised.
   - `popNatUpTo` is bounded by `maxN = 256` for unsigned integer keys.
   - `popMaybeCell` accepts `.null` as absent dictionary.
   - `popIntFinite` must reject non-finite/non-int key values.

3. [B3] Unsigned in-range integer key path.
   - `dictKeyBits? key n true` succeeds only for `0 ≤ key < 2^n`.
   - On success, `dictNearestWithCells` runs with `goUp = false`, `allowEq = false`, `sgnd = false` and a
     loaded dictionary cell.

4. [B4] Unsigned in-range nearest outcomes.
   - `dictNearestWithCells` miss pushes `0`.
   - Hit pushes `value`, the reconstructed key as int, and `-1`.

5. [B5] Unsigned out-of-range key branch.
   - When `dictKeyBits?` fails:
     - `cond = (0 ≤ key) != goUp`.
     - With `goUp = false` (PREV), `cond` is true for non-negative keys.
     - Negative keys take the immediate miss path.
     - Non-negative keys continue to the min/max fallback path.

6. [B6] Min/max fallback path for non-negative out-of-range keys.
   - `dictMinMaxWithCells` is called with `fetchMax = true`, `invertFirst = false` and `sgnd = false`.
   - Fallback hit pushes `value`, key int, and `-1`.
   - Fallback miss pushes `0`.

7. [B7] Dictionary structure errors.
   - Both nearest and minmax traversals can throw `.dictErr`; loaded cells must be recorded before erroring out.

8. [B8] Assembler / decoder boundaries.
   - `.dictGetNear 14` must assemble to `0xF47E`.
   - Assembler must reject args outside `[4,15]`.
   - Decoder must map `0xF474..0xF47F` to `.dictGetNear` and reject
     `0xF480` and truncated prefixes.

9. [B9] Gas accounting.
   - Exact gas check (exact vs exact-1) for miss path.
   - Exact gas check for hit path (base + `cellCreateGasPrice`, as observed for this opcode family).
   - Out-of-gas minus-one failures must be validated.

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/ 

private def suiteId : InstrId :=
  { name := "DICTUGETPREV" }

private def instr : Instr :=
  .dictGetNear 14

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

private def mkUnsignedSliceDict! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
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

private def dict8A : Value :=
  .cell <| mkUnsignedSliceDict! "dict8A" 8 #[(0, valueA), (3, valueB), (128, valueC), (200, valueD)]

private def dict8B : Value :=
  .cell <| mkUnsignedSliceDict! "dict8B" 8 #[(255, valueA)]

private def dictSingle8 : Value :=
  .cell <| mkUnsignedSliceDict! "dictSingle8" 8 #[(3, valueB)]

private def dict0 : Value :=
  .cell <| mkUnsignedSliceDict! "dict0" 0 #[(0, valueA)]

private def dict256Pair : Value :=
  .cell <| mkUnsignedSliceDict! "dict256Pair" 256 #[(0, valueA), (maxInt257, valueD)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def dictNull : Value := .null

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def hitGas : Int := baseGas + cellCreateGasPrice
private def hitGasMinusOne : Int := if hitGas > 0 then hitGas - 1 else 0

private def rawOpcodeF47C : Cell := Cell.mkOrdinary (natToBits 0xF47C 16) #[]
private def rawOpcodeF47E : Cell := Cell.mkOrdinary (natToBits 0xF47E 16) #[]
private def rawOpcodeF47A : Cell := Cell.mkOrdinary (natToBits 0xF47A 16) #[]
private def rawOpcodeF47F : Cell := Cell.mkOrdinary (natToBits 0xF47F 16) #[]
private def rawOpcodeF474 : Cell := Cell.mkOrdinary (natToBits 0xF474 16) #[]
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

private def expectHitShape (label : String) (res : Except Excno (Array Value)) (expectedKey : Int) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.size != 3 then
        throw (IO.userError s!"{label}: expected 3 stack items, got {st.size}")
      match st[0]?, st[1]?, st[2]? with
      | some (Value.slice _), some (Value.int (IntVal.num k)), some (Value.int (IntVal.num flag)) =>
          if k != expectedKey then
            throw (IO.userError s!"{label}: expected key {expectedKey}, got {k}")
          if flag != -1 then
            throw (IO.userError s!"{label}: expected success flag -1, got {flag}")
      | _, _, _ =>
          throw (IO.userError s!"{label}: unexpected stack shape {reprStr st}")

private def genDICTUGETPREV (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/hit-1" (stack3 1 dict8A 8), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/hit-4" (stack3 4 dict8A 8), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/hit-129" (stack3 129 dict8A 8), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/hit-255" (stack3 255 dict8A 8), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/miss-smallest" (stack3 0 dict8A 8), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/miss-empty" (stack3 42 dictNull 8), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/fallback/oob-pos-256" (stack3 256 dict8A 8), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/fallback/oob-pos-big" (stack3 1_000 dict8A 8), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/fallback/oob-pos-max" (stack3 (maxInt257 + 1) dict256Pair 256), rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/fallback/oob-pos-0-0" (stack3 1 dict0 0), rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/fallback/oob-pos-empty-0" (stack3 1 dictNull 0), rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/miss/negative" (stack3 (-1) dict8A 8), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss/negative-empty" (stack3 (-1) dictNull 8), rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/underflow-one" (#[].push (intV 7)), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/type-key" (#[.slice valueA, dict8A, intV 8]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-dict" (stack3 1 (.int (.num 0)) 8), rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/type-n" #[intV 1, dict8A, .tuple #[]], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/n-neg" (stack3 1 dict8A (-1)), rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/noob" (stack3 1 dict8A 257), rng1)
    else if shape = 20 then
      (mkCodeCase "fuzz/raw/f47e" (stack3 1 dict8A 8) rawOpcodeF47E, rng1)
    else
      (mkCodeCase "fuzz/raw/truncated" #[] rawTruncated8, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "dispatch/fallback" (runDispatchFallback (stack3 7 dict8A 8))
          ((stack3 7 dict8A 8).push (intV dispatchSentinel))
    },
    { name := "unit/opcode/assemble/exact" -- [B8]
      run := do
        let c := assembleNoRefCell! "dictugEtprev/asm" #[instr]
        if c.bits = natToBits 0xF47E 16 then
          pure ()
        else
          throw (IO.userError s!"expected 0xF47E bits, got {c.bits}")
    },
    { name := "unit/opcode/assemble/reject-low-args" -- [B8]
      run := do
        match assembleCp0 [Instr.dictGetNear 3] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted args4=3")
        | .error _ => pure ()
    },
    { name := "unit/opcode/assemble/reject-high-args" -- [B8]
      run := do
        match assembleCp0 [Instr.dictGetNear 16] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted args4=16")
        | .error _ => pure ()
    },
    { name := "unit/direct/hit/below-zero" -- [B3][B4]
      run := do
        expectHitShape "direct/hit/1" (runDirect (stack3 1 dict8A 8)) 0
    },
    { name := "unit/direct/hit/after-small" -- [B3][B4]
      run := do
        expectHitShape "direct/hit/4" (runDirect (stack3 4 dict8A 8)) 3
    },
    { name := "unit/direct/hit/above-8bit" -- [B3][B4]
      run := do
        expectHitShape "direct/hit/129" (runDirect (stack3 129 dict8A 8)) 128
    },
    { name := "unit/direct/hit/top-range" -- [B3][B4]
      run := do
        expectHitShape "direct/hit/255" (runDirect (stack3 255 dict8A 8)) 200
    },
    { name := "unit/direct/fallback/oob-pos" -- [B5][B6][B7]
      run := do
        expectHitShape "direct/fallback/oob-pos" (runDirect (stack3 256 dict8A 8)) 200
    },
    { name := "unit/direct/fallback/oob-zero-width" -- [B5][B6][B7]
      run := do
        expectHitShape "direct/fallback/zero-width-pos" (runDirect (stack3 1 dict0 0)) 0
    },
    { name := "unit/direct/miss/smallest" -- [B4]
      run := do
        expectOkStack "direct/miss-smallest" (runDirect (stack3 0 dict8A 8))
          #[intV 0]
    },
    { name := "unit/direct/miss/negative" -- [B5]
      run := do
        expectOkStack "direct/miss/negative" (runDirect (stack3 (-1) dict8A 8))
          #[intV 0]
    },
    { name := "unit/direct/miss/empty" -- [B3]
      run := do
        expectOkStack "direct/miss-empty" (runDirect (stack3 42 dictNull 8))
          #[intV 0]
    },
    { name := "unit/direct/err/malformed-nearest" -- [B7]
      run := do
        expectErr "direct/malformed-nearest" (runDirect (stack3 7 (.cell malformedDict) 8)) .cellUnd
    },
    { name := "unit/direct/err/malformed-minmax" -- [B7]
      run := do
        expectOkStack "direct/malformed-minmax" (runDirect (stack3 (-1) (.cell malformedDict) 8)) #[intV 0]
    },
    { name := "unit/decode/chain-and-boundary" -- [B8]
      run := do
        let s0 :=
          Slice.ofCell <| Cell.mkOrdinary
            (rawOpcodeF474.bits ++ rawOpcodeF47A.bits ++ rawOpcodeF47C.bits ++ rawOpcodeF47E.bits ++ rawOpcodeF47F.bits) #[]
        let s1 ← expectDecodeStep "decode/f474" s0 (.dictGetNear 4) 16
        let s2 ← expectDecodeStep "decode/f47a" s1 (.dictGetNear 10) 16
        let s3 ← expectDecodeStep "decode/f47c" s2 (.dictGetNear 12) 16
        let s4 ← expectDecodeStep "decode/f47e" s3 (.dictGetNear 14) 16
        let s5 ← expectDecodeStep "decode/f47f" s4 (.dictGetNear 15) 16
        if s5.bitsRemaining + s5.refsRemaining != 0 then
          throw (IO.userError "decode chain did not consume full stream")
        match decodeCp0WithBits (Slice.ofCell rawOpcodeF480) with
        | .error _ => pure ()
        | .ok (instr, _bits, _) =>
            throw (IO.userError s!"decode unexpectedly accepted 0xF480 as {instr}")
    },
    { name := "unit/decode/truncated" -- [B8]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode") }
  ]
  oracle := #[
    mkCase "ok/hit/1" (stack3 1 dict8A 8), -- [B3][B4]
    mkCase "ok/hit/3" (stack3 3 dict8A 8), -- [B3][B4]
    mkCase "ok/hit/4" (stack3 4 dict8A 8), -- [B3][B4]
    mkCase "ok/hit/5" (stack3 5 dict8A 8), -- [B3][B4]
    mkCase "ok/hit/129" (stack3 129 dict8A 8), -- [B3][B4]
    mkCase "ok/hit/200" (stack3 200 dict8A 8), -- [B3][B4]
    mkCase "ok/hit/255" (stack3 255 dict8A 8), -- [B3][B4]
    mkCase "ok/miss/smallest" (stack3 0 dict8A 8), -- [B4]
    mkCase "ok/miss/small-dict" (stack3 0 dict8B 8), -- [B4]
    mkCase "ok/miss/empty" (stack3 42 dictNull 8), -- [B3][B5]
    mkCase "ok/miss/negative" (stack3 (-10) dict8A 8), -- [B5]
    mkCase "ok/miss/negative-empty" (stack3 (-10) dictNull 8), -- [B5]
    mkCase "ok/oob-pos-256" (stack3 256 dict8A 8), -- [B5][B6][B7]
    mkCase "ok/oob-pos-257" (stack3 257 dict8A 8), -- [B5][B6][B7]
    mkCase "ok/oob-pos-max" (stack3 (maxInt257) dict256Pair 256), -- [B5][B6][B7]
    mkCase "ok/oob-pos-max+1" (stack3 (maxInt257 + 1) dict256Pair 256), -- [B5][B6][B7]
    mkCase "ok/fallback/zero-width-pos" (stack3 1 dict0 0), -- [B5][B6][B7]
    mkCase "ok/fallback/zero-width-empty" (stack3 1 dictNull 0), -- [B5][B6]
    mkCase "ok/malformed/dict-nearest" (stack3 1 (.cell malformedDict) 8), -- [B7]
    mkCase "ok/malformed/dict-minmax" (stack3 (-1) (.cell malformedDict) 8), -- [B7]
    mkCodeCase "ok/fuzz/raw/0xf47a" (stack3 7 dict8A 8) rawOpcodeF47A, -- [B8]
    mkCodeCase "ok/fuzz/raw/0xf47c" (stack3 7 dict8A 8) rawOpcodeF47C, -- [B8]
    mkCodeCase "ok/fuzz/raw/0xf47e" (stack3 7 dict8A 8) rawOpcodeF47E, -- [B8]
    mkCodeCase "ok/fuzz/raw/0xf47f" (stack3 7 dict8A 8) rawOpcodeF47F, -- [B8]
    mkCase "err/underflow-empty" #[], -- [B2]
    mkCase "err/underflow-one" (#[].push (intV 7)), -- [B2]
    mkCase "err/underflow-two" (stack3 7 dict8A 8 |>.take 2), -- [B2]
    mkCase "err/type-key" (#[.slice valueA, dict8A, intV 8]), -- [B2]
    mkCase "err/key-nan" (#[.int .nan, dict8A, intV 8]), -- [B2]
    mkCase "err/type-dict" (stack3 1 (.int (.num 0)) 8), -- [B2]
    mkCase "err/type-n" #[intV 1, dict8A, .tuple #[]], -- [B2]
    mkCase "err/n-negative" (stack3 1 dict8A (-1)), -- [B2]
    mkCase "err/n-too-large" (stack3 1 dict8A 257), -- [B2]
    mkCodeCase "err/code/truncated" (#[] ) rawTruncated8, -- [B8]
    mkCodeCase "err/code/invalid-next" (stack3 1 dict8A 8) rawOpcodeF480, -- [B8]
    mkCase "gas/exact-base-miss" (stack3 90 dictSingle8 8)
      #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact baseGas), -- [B9]
    mkCase "gas/exact-minus-one-miss" (stack3 90 dictSingle8 8)
      #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExactMinusOne baseGasMinusOne), -- [B9]
    mkCase "gas/exact-hit" (stack3 90 dict8A 8)
      #[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact hitGas), -- [B9]
    mkCase "gas/exact-hit-minus-one" (stack3 90 dict8A 8)
      #[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact hitGasMinusOne) -- [B9]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTUGETPREV }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETPREV
