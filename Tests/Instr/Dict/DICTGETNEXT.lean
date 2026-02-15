import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTGETNEXT

/-!
INSTRUCTION: DICTGETNEXT

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatcher branch:
   - `.dictGetNear` is handled by `execInstrDictDictGetNear`; all other opcodes are
     forwarded via `next`.

2. [B2] Runtime preamble:
   - `checkUnderflow 3` checks the three required stack values.
   - `n` is parsed by `popNatUpTo 1023`.
   - `dictCell?` is parsed by `popMaybeCell` and accepts `.null` or `.cell`.
   - Key is parsed by `popSlice`.
   - Underflow/type/range errors follow standard VM behavior.

3. [B3] Assembler encoding validation:
   - `.dictGetNear` accepts only `4 ≤ args4 ≤ 15`.
   - `DICTGETNEXT` (`args4 = 4`) assembles to `0xF474`.
   - Out-of-range args values must fail with `.rangeChk`.

4. [B4] Decoder behavior:
   - `0xF474..0xF47F` decode to `.dictGetNear args4`.
   - `0xF47F` is accepted as an in-family neighbor.
   - `0xF480` and truncated prefixes are rejected.

5. [B5] Key-length branch:
   - The hint slice must have at least `n` bits, otherwise `.cellUnd`.
   - Boundary around `n=1023` is explicit: any hint shorter than 1023 bits must fail.

6. [B6] Strict-next semantics (allowEq=false):
   - For matching keys (e.g. key==2), lookup returns the next greater key (e.g. 5),
     not the equal key.
   - If there is no greater key, path yields miss.

7. [B7] Dict traversal success and miss:
   - Miss pushes only `[0]`.
   - Hit pushes `[valueSlice, keySlice, -1]`.
   - Key slice on hit is reconstructed from discovered raw key bits.

8. [B8] Dictionary traversal errors:
   - Malformed dictionary structures can fail as `.dictErr`.

9. [B9] Gas accounting:
   - Base execution has fixed cost.
   - Hit path includes extra `cellCreateGasPrice`.
   - Exact and exact-minus-one checks are required.

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTGETNEXT" }

private def instr : Instr :=
  .dictGetNear 4

private def dispatchSentinel : Int :=
  9077

private def mkSlice (width : Nat) (value : Nat) : Slice :=
  mkSliceFromBits (natToBits value width)

private def mkSliceV (width : Nat) (value : Nat) : Value :=
  .slice (mkSlice width value)

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Nat × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) => root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def valueA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xE5 8)

private def dictSlice4 : Value :=
  .cell <| mkDictSetSliceRoot! "dictSlice4" 4 #[(0, valueA), (2, valueB), (5, valueC), (12, valueD)]

private def dictSlice8 : Value :=
  .cell <| mkDictSetSliceRoot! "dictSlice8" 8 #[(0, valueB), (128, valueC), (200, valueD)]

private def dictSlice0 : Value :=
  .cell <| mkDictSetSliceRoot! "dictSlice0" 0 #[(0, valueE)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def rawOpcode (w16 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w16 16) #[]

private def rawF474 : Cell := rawOpcode 0xF474
private def rawF475 : Cell := rawOpcode 0xF475
private def rawF47F : Cell := rawOpcode 0xF47F
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def hitGas : Int := baseGas + cellCreateGasPrice
private def hitGasMinusOne : Int := if hitGas > 0 then hitGas - 1 else 0

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

private def expectAssembleRangeErr (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected .rangeChk, got success")
  | .error _ =>
      pure ()

private def addSuffixToCaseName (name : String) (rng0 : StdGen) : String × StdGen :=
  let (sfx, rng1) := randNat rng0 0 999_999
  (s!"{name}/{sfx}", rng1)

def genDictGetNextFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (baseCase, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/err/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/err/underflow/one" (#[.slice (mkSlice 4 0)]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/err/underflow/two" (#[.slice (mkSlice 4 0), dictSlice4]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/err/key-type" (#[.tuple #[], dictSlice4, intV 4]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/err/dict-type" (#[.slice (mkSlice 4 0), .int (.num 0), intV 4]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/n-type" (#[.slice (mkSlice 4 0), dictSlice4, .tuple #[]]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/n-nan" (#[.slice (mkSlice 4 0), dictSlice4, .int .nan]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/n-negative" (#[.slice (mkSlice 4 0), dictSlice4, intV (-1)]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/n-too-large" (#[.slice (mkSlice 4 0), dictSlice4, intV 1024]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/key-too-short" (#[.slice (mkSlice 3 5), dictSlice4, intV 4]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/key-too-short-maxn" (#[.slice (mkSlice 1022 1), dictSlice8, intV 1023]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/hit4-eq" (#[.slice (mkSlice 4 2), dictSlice4, intV 4]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/hit4-next" (#[.slice (mkSlice 4 3), dictSlice4, intV 4]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/hit4-upper" (#[.slice (mkSlice 4 7), dictSlice4, intV 4]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/miss4-top" (#[.slice (mkSlice 4 12), dictSlice4, intV 4]), rng1)
    else if shape = 15 then
      (mkCase "fuzz/ok/miss4-above" (#[.slice (mkSlice 4 15), dictSlice4, intV 4]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/ok/hit8-eq" (#[.slice (mkSlice 8 0), dictSlice8, intV 8]), rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/hit8-next" (#[.slice (mkSlice 8 129), dictSlice8, intV 8]), rng1)
    else if shape = 18 then
      (mkCase "fuzz/ok/miss8-top" (#[.slice (mkSlice 8 255), dictSlice8, intV 8]), rng1)
    else if shape = 19 then
      (mkCase "fuzz/ok/miss8-empty" (#[.slice (mkSlice 8 1), .null, intV 8]), rng1)
    else if shape = 20 then
      (mkCase "fuzz/ok/miss0" (#[.slice (mkSlice 0 0), dictSlice0, intV 0]), rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/malformed-root" (#[.slice (mkSlice 4 0), .cell malformedDict, intV 4]), rng1)
    else if shape = 22 then
      (mkCaseCode "fuzz/raw/f474" (#[.slice (mkSlice 4 0), dictSlice4, intV 4]) rawF474, rng1)
    else if shape = 23 then
      (mkCaseCode "fuzz/raw/f475" (#[.slice (mkSlice 4 0), dictSlice4, intV 4]) rawF475, rng1)
    else if shape = 24 then
      (mkCaseCode "fuzz/raw/f47f" (#[.slice (mkSlice 4 0), dictSlice4, intV 4]) rawF47F, rng1)
    else if shape = 25 then
      (mkCaseCode "fuzz/code/truncated" (#[.slice (mkSlice 4 0), dictSlice4, intV 4]) rawTruncated8, rng1)
    else if shape = 26 then
      (mkCase "fuzz/ok/gas/hit-exact"
        (#[.slice (mkSlice 4 2), dictSlice4, intV 4])
        (#[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact hitGas), rng1)
    else if shape = 27 then
      (mkCase "fuzz/ok/gas/miss-exact"
        (#[.slice (mkSlice 8 255), .null, intV 8])
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 28 then
      (mkCase "fuzz/ok/gas/hit-minus-one"
        (#[.slice (mkSlice 4 2), dictSlice4, intV 4])
        (#[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact hitGasMinusOne), rng1)
    else if shape = 29 then
      (mkCase "fuzz/ok/gas/miss-minus-one"
        (#[.slice (mkSlice 8 255), .null, intV 8])
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact baseGasMinusOne), rng1)
    else
      (mkCase "fuzz/ok/hit4-edge" (#[.slice (mkSlice 4 9), dictSlice4, intV 4]), rng1)
  let (name', rng3) := addSuffixToCaseName baseCase.name rng2
  ({ baseCase with name := name' }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := #[.slice (mkSlice 4 2), dictSlice4, intV 4]
        let expected := stack.push (intV dispatchSentinel)
        expectOkStack "unit/dispatch/fallback" (runDispatchFallback stack) expected
    },
    { name := "unit/assemble/ok" -- [B3]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF474 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF474 encoding, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTGETNEXT failed: {reprStr e}")
    },
    { name := "unit/assemble/reject-lower-args4" -- [B3]
      run := do
        expectAssembleRangeErr "unit/assemble/reject-lower-args4" (Instr.dictGetNear 3)
    },
    { name := "unit/assemble/reject-upper-args4" -- [B3]
      run := do
        expectAssembleRangeErr "unit/assemble/reject-upper-args4" (Instr.dictGetNear 16)
    },
    { name := "unit/direct/hit-next-eq" -- [B6][B7]
      run := do
        let st ←
          match runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 4 2), dictSlice4, intV 4]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"direct-hit-next-eq: expected success, got {reprStr e}")
        match st with
        | #[.slice _, .slice k, Value.int (.num (-1))] =>
            if k == mkSlice 4 5 then pure ()
            else throw (IO.userError s!"direct-hit-next-eq: expected key 5, got {reprStr k}")
        | _ => throw (IO.userError s!"direct-hit-next-eq: unexpected stack {reprStr st}")
    },
    { name := "unit/direct/hit-next-higher" -- [B6][B7]
      run := do
        let st ←
          match runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 4 9), dictSlice4, intV 4]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"direct-hit-next-higher: expected success, got {reprStr e}")
        match st with
        | #[.slice _, .slice k, Value.int (.num (-1))] =>
            if k == mkSlice 4 12 then pure ()
            else throw (IO.userError s!"direct-hit-next-higher: expected key 12, got {reprStr k}")
        | _ => throw (IO.userError s!"direct-hit-next-higher: unexpected stack {reprStr st}")
    },
    { name := "unit/direct/miss4-max" -- [B7]
      run := do
        expectOkStack "direct-miss4-max" (runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 4 15), dictSlice4, intV 4])) #[intV 0]
    },
    { name := "unit/direct/hit8-eq" -- [B6][B7]
      run := do
        let st ←
          match runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 8 0), dictSlice8, intV 8]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"direct-hit8-eq: expected success, got {reprStr e}")
        match st with
        | #[.slice _, .slice k, Value.int (.num (-1))] =>
            if k == mkSlice 8 128 then pure ()
            else throw (IO.userError s!"direct-hit8-eq: expected key 128, got {reprStr k}")
        | _ => throw (IO.userError s!"direct-hit8-eq: unexpected stack {reprStr st}")
    },
    { name := "unit/direct/hit8-edge" -- [B6][B7]
      run := do
        let st ←
          match runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 8 129), dictSlice8, intV 8]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"direct-hit8-edge: expected success, got {reprStr e}")
        match st with
        | #[.slice _, .slice k, Value.int (.num (-1))] =>
            if k == mkSlice 8 200 then pure ()
            else throw (IO.userError s!"direct-hit8-edge: expected key 200, got {reprStr k}")
        | _ => throw (IO.userError s!"direct-hit8-edge: unexpected stack {reprStr st}")
    },
    { name := "unit/direct/miss8" -- [B7]
      run := do
        expectOkStack "direct-miss8" (runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 8 255), dictSlice8, intV 8])) #[intV 0]
    },
    { name := "unit/direct/miss-empty-dict" -- [B7]
      run := do
        expectOkStack "direct-miss-empty" (runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 4 0), .null, intV 4])) #[intV 0]
    },
    { name := "unit/direct/n0-miss" -- [B6][B5]
      run := do
        expectOkStack "direct-n0-miss" (runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 0 0), dictSlice0, intV 0])) #[intV 0]
    },
    { name := "unit/direct/key-too-short" -- [B5]
      run := do
        expectErr "direct-key-too-short" (runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 3 5), dictSlice4, intV 4])) .cellUnd
    },
    { name := "unit/direct/dict-err" -- [B8]
      run := do
        match runHandlerDirect execInstrDictDictGetNear instr (#[.slice (mkSlice 4 0), .cell malformedDict, intV 4]) with
        | .error .dictErr => pure ()
        | .error .cellUnd => pure ()
        | .error e => throw (IO.userError s!"direct-dict-err: expected dictErr or cellUnd, got {reprStr e}")
        | .ok st => throw (IO.userError s!"direct-dict-err: expected error, got stack {reprStr st}")
    },
    { name := "unit/decode/family-chain" -- [B4]
      run := do
        let packed :=
          Cell.mkOrdinary (rawF474.bits ++ rawF475.bits ++ rawF47F.bits) #[]
        let s0 := Slice.ofCell packed
        let s1 ← expectDecodeStep "decode/F474" s0 (.dictGetNear 4) 16
        let s2 ← expectDecodeStep "decode/F475" s1 (.dictGetNear 5) 16
        let _ ← expectDecodeStep "decode/F47F" s2 (.dictGetNear 15) 16
        pure ()
    },
    { name := "unit/decode/truncated" -- [B4]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode")
    }
  ]
  oracle := #[
    mkCase "err/underflow/empty" #[] -- [B2]
      ,
    mkCase "err/underflow/one" (#[.slice (mkSlice 4 0)]) -- [B2]
      ,
    mkCase "err/underflow/two" (#[.slice (mkSlice 4 0), dictSlice4]) -- [B2]
      ,
    mkCase "err/key-type" (#[.tuple #[], dictSlice4, intV 4]) -- [B2]
      ,
    mkCase "err/dict-type" (#[.slice (mkSlice 4 0), .int (.num 0), intV 4]) -- [B2]
      ,
    mkCase "err/n-type" (#[.slice (mkSlice 4 0), dictSlice4, .tuple #[]]) -- [B2]
      ,
    mkCase "err/n-nan" (#[.slice (mkSlice 4 0), dictSlice4, .int .nan]) -- [B2]
      ,
    mkCase "err/n-negative" (#[.slice (mkSlice 4 0), dictSlice4, intV (-1)]) -- [B2]
      ,
    mkCase "err/n-too-large" (#[.slice (mkSlice 4 0), dictSlice4, intV 1024]) -- [B2]
      ,
    mkCase "err/key-too-short" (#[.slice (mkSlice 3 5), dictSlice4, intV 4]) -- [B5]
      ,
    mkCase "err/key-too-short-maxn" (#[.slice (mkSlice 1022 1), dictSlice8, intV 1023]) -- [B5]
      ,
    mkCase "ok/hit4-eq" (#[.slice (mkSlice 4 2), dictSlice4, intV 4]) -- [B6][B7]
      ,
    mkCase "ok/hit4-higher" (#[.slice (mkSlice 4 7), dictSlice4, intV 4]) -- [B6][B7]
      ,
    mkCase "ok/hit4-edge-9" (#[.slice (mkSlice 4 9), dictSlice4, intV 4]) -- [B6][B7]
      ,
    mkCase "ok/miss4-top" (#[.slice (mkSlice 4 15), dictSlice4, intV 4]) -- [B7]
      ,
    mkCase "ok/miss4-middle" (#[.slice (mkSlice 4 13), dictSlice4, intV 4]) -- [B7]
      ,
    mkCase "ok/hit8-eq" (#[.slice (mkSlice 8 0), dictSlice8, intV 8]) -- [B6][B7]
      ,
    mkCase "ok/hit8-next" (#[.slice (mkSlice 8 129), dictSlice8, intV 8]) -- [B6][B7]
      ,
    mkCase "ok/miss8-top" (#[.slice (mkSlice 8 255), dictSlice8, intV 8]) -- [B7]
      ,
    mkCase "ok/miss8-empty" (#[.slice (mkSlice 8 8), .null, intV 8]) -- [B7]
      ,
    mkCase "ok/miss0-arg" (#[.slice (mkSlice 0 0), dictSlice0, intV 0]) -- [B6][B5]
      ,
    mkCase "ok/miss-empty" (#[.slice (mkSlice 4 0), .null, intV 4]) -- [B7]
      ,
    mkCase "err/dict-malformed" (#[.slice (mkSlice 4 0), .cell malformedDict, intV 4]) -- [B8]
      ,
    mkCaseCode "ok/code/f474" (#[.slice (mkSlice 4 0), dictSlice4, intV 4]) rawF474 -- [B4]
      ,
    mkCaseCode "ok/code/f475" (#[.slice (mkSlice 4 0), dictSlice4, intV 4]) rawF475 -- [B4]
      ,
    mkCaseCode "ok/code/f47f" (#[.slice (mkSlice 4 0), dictSlice4, intV 4]) rawF47F -- [B4]
      ,
    mkCaseCode "err/code/raw-truncated" (#[.slice (mkSlice 4 0), dictSlice4, intV 4]) rawTruncated8 -- [B4]
      ,
    mkCase "gas/base-miss-exact" (#[.slice (mkSlice 8 255), .null, intV 8])
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas), -- [B9]
    mkCase "gas/base-miss-minus-one" (#[.slice (mkSlice 8 255), .null, intV 8])
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGasMinusOne), -- [B9]
    mkCase "gas/hit-exact" (#[.slice (mkSlice 4 2), dictSlice4, intV 4])
      (#[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGas), -- [B9]
    mkCase "gas/hit-minus-one" (#[.slice (mkSlice 4 2), dictSlice4, intV 4])
      (#[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGasMinusOne) -- [B9]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictGetNextFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTGETNEXT
