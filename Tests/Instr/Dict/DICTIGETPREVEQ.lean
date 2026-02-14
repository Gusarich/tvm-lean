import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETPREVEQ

/- 
INSTRUCTION: DICTIGETPREVEQ

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Normal success path (hit): `n` is valid, dict pops as `Option Cell`,
   key is finite and representable as signed `n` bits; nearest-predecessor lookup
   finds a value, then pushes value slice, matched key int, and `-1`.
2. [B2] In-range miss path (normal predecessor search): no predecessor exists
   for valid `i`; pushes only `0`.
3. [B3] Out-of-range negative key fallback path: representability fails for
   negative `i`, so branch via `dictMinMaxWithCells` (fetch max). This path can
   still hit or miss depending on dict content.
4. [B4] Out-of-range non-negative key path: representability fails for
   non-negative `i`, so the immediate "miss" path pushes `0`.
5. [B5] Runtime stack/type/range errors:
   underflow (`checkUnderflow`), non-int/invalid `n`, non-cell dict where not
   expected for `maybeCell`, and non-finite/non-int key.
6. [B6] Dictionary structural error path: malformed dict root or invalid traversal
   causes `dictNearestWithCells` / `dictMinMaxWithCells` failure.
7. [B7] Gas branch: exact-gas success and exact-gas-minus-one failure via
   `PUSHINT gas; SETGASLIMIT; DICTIGETPREVEQ`.
8. [B8] Decoder branch: fixed-point decode family `0xF474..0xF47F`
   (`dictGetNear 0..15`) and rejection outside this range.

TOTAL BRANCHES: 8

Runtime semantics, decoder, gas, and boundary categories are covered as follows:
- Runtime/branches B1-B7: explicit oracle test vectors and fuzz weighting.
- Decoder B8: unit-level decode checks for boundaries and invalid raw opcode.
- Gas: exact and exact-minus-one oracle cases plus fuzz branch.
- Range/type errors: dedicated oracle vectors plus fuzz error branch.
- No additional variable gas penalty exists in the int-key Lean branch aside from the
  static instruction budget used by exact-budget tests.
-/

private def dictGetPreveqId : InstrId := { name := "DICTIGETPREVEQ" }
private def dictGetPreveqInstr : Instr := .dictGetNear 7

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def mkSigned8Dict (pairs : Array (Int × Nat)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let key : Int := p.1
      let tag : Nat := p.2
      let bits : BitString :=
        match dictKeyBits? key 8 false with
        | some b => b
        | none => panic! s!"DICTIGETPREVEQ: key {key} out of range for n=8"
      let value : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits tag 8) #[])
      match dictSetSliceWithCells root bits value .set with
      | .ok (some r, _ok, _created, _loaded) => root := some r
      | .ok (none, _, _, _) => panic! "DICTIGETPREVEQ: dictionary set returned none"
      | .error e => panic! s!"DICTIGETPREVEQ: dictionary build failed: {e}"
    match root with
    | some d => d
    | none => Cell.empty

private def dict8A : Cell := mkSigned8Dict #[( -20, 0xA0), (-1, 0xA1), (7, 0xA2), (90, 0xA3)]
private def dict8B : Cell := mkSigned8Dict #[(1, 0xB1)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def dictGetPreveqGas : Int := computeExactGasBudget dictGetPreveqInstr
private def dictGetPreveqGasMinusOne : Int := computeExactGasBudgetMinusOne dictGetPreveqInstr
private def dictGetPreveqGasExact : OracleGasLimits := oracleGasLimitsExact dictGetPreveqGas
private def dictGetPreveqGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExact dictGetPreveqGasMinusOne

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictGetPreveqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictGetPreveqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def stack3 (key : Int) (dictCell : Value) (n : Int) : Array Value :=
  #[intV key, dictCell, intV n]

private def pickIntFrom (xs : Array Int) (rng0 : StdGen) : Int × StdGen :=
  let (idx, rng1) := randNat rng0 0 (xs.size - 1)
  match xs[idx]? with
  | some x => (x, rng1)
  | none => (0, rng1)

private def pickDictCell (rng0 : StdGen) : Value × StdGen :=
  let (tag, rng1) := randNat rng0 0 3
  if tag = 0 then
    (.null, rng1)
  else if tag = 1 then
    (.cell dict8A, rng1)
  else if tag = 2 then
    (.cell dict8B, rng1)
  else
    (.cell malformedDict, rng1)

private def genDICTIGETPREVEQ (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    -- [B1] Hit/path with in-range keys.
    let (key, rng2) := pickIntFrom #[( -20), (-1), (7), (90)] rng1
    let (dictV, rng3) := pickDictCell rng2
    ({ name := "fuzz/hit/range", instr := dictGetPreveqId, initStack := stack3 key dictV 8 }, rng3)
  else if shape = 1 then
    -- [B2] In-range predecessor fallback within non-empty dict.
    let (key, rng2) := pickIntFrom #[( -2), (6), (8), (91)] rng1
    ({ name := "fuzz/hit/fallback", instr := dictGetPreveqId, initStack := stack3 key (.cell dict8A) 8 }, rng2)
  else if shape = 2 then
    -- [B4] In-range miss in non-empty singleton.
    ({ name := "fuzz/miss/in-range", instr := dictGetPreveqId, initStack := stack3 0 (.cell dict8B) 8 }, rng1)
  else if shape = 3 then
    -- [B4] Empty dict miss with same in-range key.
    let (key, rng2) := pickIntFrom #[( -20), (7), (90)] rng1
    ({ name := "fuzz/miss/empty", instr := dictGetPreveqId, initStack := stack3 key .null 8 }, rng2)
  else if shape = 4 then
    -- [B3] Negative out-of-range key uses max/min fallback.
    let (key, rng2) := pickIntFrom #[( -130), (-200), (-129)] rng1
    let (dictV, rng3) := pickDictCell rng2
    ({ name := "fuzz/out-of-range-neg", instr := dictGetPreveqId, initStack := stack3 key dictV 8 }, rng3)
  else if shape = 5 then
    -- [B4] Positive out-of-range miss path.
    let (key, rng2) := pickIntFrom #[( 128), (130), (1_000)] rng1
    let (dictV, rng3) := pickDictCell rng2
    ({ name := "fuzz/out-of-range-pos", instr := dictGetPreveqId, initStack := stack3 key dictV 8 }, rng3)
  else if shape = 6 then
    -- [B5] Range/type errors on n.
    let (badN, rng2) := pickIntFrom #[(1024), (-1)] rng1
    ({ name := "fuzz/bad-n", instr := dictGetPreveqId, initStack := stack3 7 .null badN }, rng2)
  else if shape = 7 then
    -- [B5] Type errors and underflow variants.
    let (mode, rng2) := randNat rng1 0 4
    let stack : Array Value :=
      if mode = 0 then
        #[]
      else if mode = 1 then
        #[intV 7]
      else if mode = 2 then
        #[.null, .cell dict8A, intV 8]
      else if mode = 3 then
        #[intV 7, .int (.num 0), intV 8]
      else
        #[intV 7, .cell dict8A, .null]
    ({ name := "fuzz/type-errors", instr := dictGetPreveqId, initStack := stack }, rng2)
  else if shape = 8 then
    -- [B6] Malformed dictionary branch.
    ({ name := "fuzz/malformed-dict", instr := dictGetPreveqId, initStack := stack3 (-1) (.cell malformedDict) 8 }, rng1)
  else
    -- [B7] Gas boundary branch.
    let (exact, rng2) := randBool rng1
    if exact then
      ({ name := "fuzz/gas/exact", instr := dictGetPreveqId,
          program := #[.pushInt (.num dictGetPreveqGas), .tonEnvOp .setGasLimit, dictGetPreveqInstr],
          initStack := stack3 90 (.cell dict8A) 8,
          gasLimits := dictGetPreveqGasExact }, rng2)
    else
      ({ name := "fuzz/gas/exact-minus-one", instr := dictGetPreveqId,
          program := #[.pushInt (.num dictGetPreveqGasMinusOne), .tonEnvOp .setGasLimit, dictGetPreveqInstr],
          initStack := stack3 90 (.cell dict8A) 8,
          gasLimits := dictGetPreveqGasExactMinusOne }, rng2)

def suite : InstrSuite where
  id := dictGetPreveqId
  unit := #[
    { name := "unit/decode-boundaries"
      run := do
        let c0 := assembleNoRefCell! "dictigetpreveq/asm" #[dictGetPreveqInstr]
        let _ ← expectDecodeStep "decode/asm" (Slice.ofCell c0) dictGetPreveqInstr 16
        let rawLower : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0xF474 16) #[])
        let rawUpper : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0xF47F 16) #[])
        let _ ← expectDecodeStep "decode/raw-lower" rawLower (.dictGetNear 0) 16
        let _ ← expectDecodeStep "decode/raw-upper" rawUpper (.dictGetNear 15) 16
        let rawInvalid : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0xF480 16) #[])
        match decodeCp0WithBits rawInvalid with
        | .error _ => pure ()
        | .ok (v, bits, _) =>
            throw (IO.userError s!"expected decode failure, got {reprStr v}/{bits}")
    }
  ]
  oracle := #[
    mkCase "ok/hit-neg-20" (stack3 (-20) (.cell dict8A) 8), -- [B1]
    mkCase "ok/hit-neg-1" (stack3 (-1) (.cell dict8A) 8), -- [B1]
    mkCase "ok/hit-7" (stack3 7 (.cell dict8A) 8), -- [B1]
    mkCase "ok/hit-90" (stack3 90 (.cell dict8A) 8), -- [B1]
    mkCase "ok/hit-singleton-1" (stack3 1 (.cell dict8B) 8), -- [B1]
    mkCase "ok/fallback-neg-2" (stack3 (-2) (.cell dict8A) 8), -- [B2]
    mkCase "ok/fallback-6" (stack3 6 (.cell dict8A) 8), -- [B2]
    mkCase "ok/fallback-8" (stack3 8 (.cell dict8A) 8), -- [B2]
    mkCase "ok/fallback-91" (stack3 91 (.cell dict8A) 8), -- [B2]
    mkCase "ok/fallback-neg-overflow-hit" (stack3 (-130) (.cell dict8A) 8), -- [B3]
    mkCase "ok/fallback-neg-overflow-empty" (stack3 (-130) .null 8), -- [B3]
    mkCase "ok/miss-in-range-singleton" (stack3 (-2) (.cell dict8B) 8), -- [B4]
    mkCase "ok/miss-empty-5" (stack3 5 .null 8), -- [B4]
    mkCase "ok/miss-empty-90" (stack3 90 .null 8), -- [B4]
    mkCase "ok/miss-pos-out-128" (stack3 128 (.cell dict8A) 8), -- [B4]
    mkCase "ok/miss-pos-out-large" (stack3 1_000 (.cell dict8A) 8), -- [B4]
    mkCase "err/underflow-empty" #[], -- [B5]
    mkCase "err/underflow-one" #[.int (.num 7)], -- [B5]
    mkCase "err/underflow-two" #[.int (.num 7), .null], -- [B5]
    mkCase "err/range-n-too-large" (stack3 (-1) .null 1024), -- [B5]
    mkCase "err/range-n-negative" (stack3 (-1) .null (-1)), -- [B5]
    mkCase "err/key-type" #[.null, .cell dict8A, intV 8], -- [B5]
    mkCase "err/key-nan" #[.int .nan, .cell dict8A, intV 8], -- [B5]
    mkCase "err/dict-type" (stack3 (-1) (.int (.num 0)) 8), -- [B5]
    mkCase "err/n-type" #[.int (.num 7), .cell dict8A, .null], -- [B5]
    mkCase "err/malformed-dict" (stack3 (-1) (.cell malformedDict) 8), -- [B6]
    mkCase "err/malformed-dict-other" (stack3 7 (.cell malformedDict) 1), -- [B6]
    mkCase "gas/exact-success" (stack3 90 (.cell dict8A) 8)
      #[.pushInt (.num dictGetPreveqGas), .tonEnvOp .setGasLimit, dictGetPreveqInstr]
      dictGetPreveqGasExact, -- [B7]
    mkCase "gas/exact-minus-one" (stack3 90 (.cell dict8A) 8)
      #[.pushInt (.num dictGetPreveqGasMinusOne), .tonEnvOp .setGasLimit, dictGetPreveqInstr]
      dictGetPreveqGasExactMinusOne, -- [B7]
    mkCase "gas/exact-minus-one-hit-2" (stack3 (-1) (.cell dict8A) 8)
      #[.pushInt (.num (dictGetPreveqGas - 1)), .tonEnvOp .setGasLimit, dictGetPreveqInstr]
      dictGetPreveqGasExactMinusOne -- [B7]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 500
      gen := genDICTIGETPREVEQ }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETPREVEQ
