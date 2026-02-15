import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTGETNEXTEQ

/-!
INSTRUCTION: DICTGETNEXTEQ

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatcher behavior:
   - `execInstrDictDictGetNear` handles only `.dictGetNear args4` and defers others to `next`.

2. [B2] Runtime preamble:
   - `checkUnderflow 3` rejects short stacks.
   - `n` is read with `popNatUpTo 1023`.
   - `dictCell?` is loaded with `popMaybeCell` (only `.null`/`.cell` accepted).
   - Key hint must be `popSlice`.
   - `n`/type errors and negative/non-nat bounds are fatal.

3. [B3] Assembler encoding:
   - `.dictGetNear 5` (non-int next-eq) must encode to `0xF475`.
   - `.dictGetNear` rejects args4 `<4` and `>15` with `rangeChk`.
   - Decoder treats `0xF474..0xF47F` as `.dictGetNear (w16 &&& 0xf)` and consumes 16 bits.

4. [B4] Slice-key branch:
   - For this instruction (`args4 = 5`), `intKey = false`; only slice-key handling is executed.
   - If hint has fewer than `n` bits, execution throws `cellUnd`.

5. [B5] `dictNearest` hit/miss outcomes:
   - On malformed dictionary access, `.dictErr` propagates.
   - On miss, push `0`.
   - On hit, push `(value, key-as-slice, -1)`.

6. [B6] Dictionary mutation state after lookup:
   - On hit, a fresh key slice is reconstructed from raw key bits and pushed.

7. [B7] Base and success gas behavior:
   - Exact base gas must match hit-miss behavior.
   - Exact-base-minus-one must fail with OOG.
   - On hit, result construction consumes an extra `cellCreateGasPrice`.

TOTAL BRANCHES: 7

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTGETNEXTEQ" }

private def instr : Instr := .dictGetNear 5

private def dispatchSentinel : Int := 9077

private def valueA : Slice := mkSliceFromBits (natToBits 0xA5 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xE5 8)

private def mkSlice (width : Nat) (value : Nat) : Slice :=
  mkSliceFromBits (natToBits value width)

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
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
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def dictSlice4 : Value :=
  .cell <| mkDictSetSliceRoot! "dictSlice4" 4 #[(0, valueA), (2, valueB), (7, valueC), (12, valueD)]

private def dictSlice8 : Value :=
  .cell <| mkDictSetSliceRoot! "dictSlice8" 8 #[(0, valueA), (128, valueB), (200, valueC)]

private def dictSlice0 : Value :=
  .cell <| mkDictSetSliceRoot! "dictSlice0" 0 #[(0, valueE)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]
private def dictNull : Value := .null

private def exactGas : Int := computeExactGasBudget instr
private def exactGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def hitGas : Int := exactGas + cellCreateGasPrice
private def hitGasMinusOne : Int := if hitGas > 0 then hitGas - 1 else 0

private def rawOpcode (w16 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w16 16) #[]

private def rawF474 : Cell := rawOpcode 0xF474
private def rawF475 : Cell := rawOpcode 0xF475
private def rawF476 : Cell := rawOpcode 0xF476
private def rawF477 : Cell := rawOpcode 0xF477
private def rawF47F : Cell := rawOpcode 0xF47F
private def rawF47Trunc8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

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

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetNear instr stack

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetNear .add (VM.push (intV dispatchSentinel)) stack

private def addSuffixToCaseName (name : String) (rng0 : StdGen) : String × StdGen :=
  let (sfx, rng1) := randNat rng0 0 999_999
  (s!"{name}/{sfx}", rng1)

def genDictGetNextEqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (baseCase, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/underflow/one" (#[ .slice (mkSlice 4 0) ]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/underflow/two" (#[ .slice (mkSlice 4 1), dictSlice4 ]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/err/key-type" (#[ .int (.num 1), dictSlice4, intV 4 ]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/err/dict-type" (#[ .slice (mkSlice 4 0), .tuple #[], intV 4 ]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/n-type" (#[ .slice (mkSlice 4 0), dictSlice4, .int .nan ]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/n-negative" (#[ .slice (mkSlice 4 0), dictSlice4, intV (-1) ]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/n-too-large" (#[ .slice (mkSlice 4 0), dictSlice4, intV 1024 ]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/key-too-short" (#[ .slice (mkSlice 3 5), dictSlice4, intV 4 ]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/key-too-short-maxn" (#[ .slice (mkSlice 8 1), dictSlice8, intV 1023 ]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/hit4-eq" (#[ .slice (mkSlice 4 2), dictSlice4, intV 4 ]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/hit4-near" (#[ .slice (mkSlice 4 5), dictSlice4, intV 4 ]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss4" (#[ .slice (mkSlice 4 15), dictSlice4, intV 4 ]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/miss-empty" (#[ .slice (mkSlice 4 7), dictNull, intV 4 ]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/hit8-eq" (#[ .slice (mkSlice 8 128), dictSlice8, intV 8 ]), rng1)
    else if shape = 15 then
      (mkCase "fuzz/ok/hit8-near" (#[ .slice (mkSlice 8 129), dictSlice8, intV 8 ]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/ok/miss8" (#[ .slice (mkSlice 8 255), dictSlice8, intV 8 ]), rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/hit0" (#[ .slice (mkSlice 0 0), dictSlice0, intV 0 ]), rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/malformed-root" (#[ .slice (mkSlice 8 1), .cell malformedDict, intV 8 ]), rng1)
    else if shape = 19 then
      (mkCase
        "fuzz/gas/base-miss-exact"
        (#[ .slice (mkSlice 8 255), dictNull, intV 8 ])
        (#[ .pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr ])
        (oracleGasLimitsExact exactGas), rng1)
    else if shape = 20 then
      (mkCase
        "fuzz/gas/base-miss-minus-one"
        (#[ .slice (mkSlice 8 255), dictNull, intV 8 ])
        (#[ .pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr ])
        (oracleGasLimitsExact exactGasMinusOne), rng1)
    else if shape = 21 then
      (mkCase
        "fuzz/gas/hit-exact"
        (#[ .slice (mkSlice 4 2), dictSlice4, intV 4 ])
        (#[ .pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr ])
        (oracleGasLimitsExact hitGas), rng1)
    else if shape = 22 then
      (mkCase
        "fuzz/gas/hit-minus-one"
        (#[ .slice (mkSlice 4 2), dictSlice4, intV 4 ])
        (#[ .pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr ])
        (oracleGasLimitsExact hitGasMinusOne), rng1)
    else if shape = 23 then
      (mkCaseCode "fuzz/code/f474" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) rawF474, rng1)
    else
      (mkCaseCode "fuzz/code/f475" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) rawF475, rng1)
  let (name', rng3) := addSuffixToCaseName baseCase.name rng2
  ({ baseCase with name := name' }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := #[.slice (mkSlice 4 1), dictSlice4, intV 4]
        let expected := stack.push (intV dispatchSentinel)
        expectOkStack "dispatch/fallback" (runDispatchFallback stack) expected
    },
    { name := "unit/assemble/ok" -- [B3]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF475 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF475 encoding, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTGETNEXTEQ failed: {reprStr e}")
    },
    { name := "unit/assemble/reject-lower-args4" -- [B3]
      run := do
        match assembleCp0 [Instr.dictGetNear 3] with
        | .ok _ =>
            throw (IO.userError "assemble accepted args4=3, expected rangeChk")
        | .error _ =>
            pure ()
    },
    { name := "unit/assemble/reject-upper-args4" -- [B3]
      run := do
        match assembleCp0 [Instr.dictGetNear 16] with
        | .ok _ =>
            throw (IO.userError "assemble accepted args4=16, expected rangeChk")
        | .error _ =>
            pure ()
    },
    { name := "unit/direct/hit" -- [B4][B5][B6]
      run := do
        let st ←
          match runDirect (#[ .slice (mkSlice 4 2), dictSlice4, intV 4 ]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"direct-hit: expected success, got {reprStr e}")
        match st with
        | #[.slice _, .slice k, Value.int (.num (-1))] =>
            if k == mkSlice 4 2 then pure ()
            else throw (IO.userError s!"direct-hit: expected key 2, got {reprStr k}")
        | _ => throw (IO.userError s!"direct-hit: unexpected stack {reprStr st}")
    },
    { name := "unit/direct/hit/high-bit" -- [B4][B5][B6]
      run := do
        let st ←
          match runDirect (#[ .slice (mkSlice 4 5), dictSlice4, intV 4 ]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"direct-hit-high-bit: expected success, got {reprStr e}")
        match st with
        | #[.slice _, .slice k, Value.int (.num (-1))] =>
            if k == mkSlice 4 7 then pure ()
            else throw (IO.userError s!"direct-hit-high-bit: expected key 7, got {reprStr k}")
        | _ => throw (IO.userError s!"direct-hit-high-bit: unexpected stack {reprStr st}")
    },
    { name := "unit/direct/miss" -- [B7]
      run := do
        expectOkStack "direct-miss" (runDirect (#[ .slice (mkSlice 8 255), dictSlice8, intV 8 ]))
          #[intV 0]
    },
    { name := "unit/direct/key-too-short" -- [B4]
      run := do
        expectErr "direct-key-too-short" (runDirect (#[ .slice (mkSlice 3 5), dictSlice4, intV 4 ])) .cellUnd
    },
    { name := "unit/decode/family-prefix" -- [B3]
      run := do
        let s0 : Slice :=
          Slice.ofCell <| Cell.mkOrdinary (rawF474.bits ++ rawF475.bits ++ rawF476.bits ++ rawF477.bits) #[]
        let s1 ← expectDecodeStep "decode/f474" s0 (.dictGetNear 4) 16
        let s2 ← expectDecodeStep "decode/f475" s1 (.dictGetNear 5) 16
        let s3 ← expectDecodeStep "decode/f476" s2 (.dictGetNear 6) 16
        let _ ← expectDecodeStep "decode/f477" s3 (.dictGetNear 7) 16
        pure ()
    },
    { name := "unit/decode/truncated-invalid" -- [B3]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawF47Trunc8) with
        | .ok _ =>
            throw (IO.userError "decode unexpectedly accepted truncated opcode")
        | .error _ =>
            pure ()
    }
  ]
  oracle := #[
    mkCase "err/underflow/empty" #[] -- [B2]
      ,
    mkCase "err/underflow/one" (#[ .slice (mkSlice 4 0) ]) -- [B2]
      ,
    mkCase "err/underflow/two" (#[ .slice (mkSlice 4 0), dictSlice4 ]) -- [B2]
      ,
    mkCase "err/key-type" (#[ .int (.num 5), dictSlice4, intV 4 ]) -- [B2]
      ,
    mkCase "err/n-type" (#[ .slice (mkSlice 4 0), dictSlice4, .int .nan ]) -- [B2]
      ,
    mkCase "err/n-negative" (#[ .slice (mkSlice 4 0), dictSlice4, intV (-1) ]) -- [B2]
      ,
    mkCase "err/n-too-large" (#[ .slice (mkSlice 4 0), dictSlice4, intV 1024 ]) -- [B2]
      ,
    mkCase "err/dict-type" (#[ .slice (mkSlice 4 0), .tuple #[], intV 4 ]) -- [B2]
      ,
    mkCase "err/key-type-not-slice" (#[ .cell (Cell.mkOrdinary (natToBits 0x2 1) #[]), dictSlice4, intV 4 ]) -- [B2]
      ,
    mkCase "err/key-too-short" (#[ .slice (mkSlice 3 5), dictSlice4, intV 4 ]) -- [B4]
      ,
    mkCase "err/key-too-short-maxn" (#[ .slice (mkSlice 8 1), dictSlice8, intV 1023 ]) -- [B4]
      ,
    mkCase "err/malformed-root" (#[ .slice (mkSlice 8 1), .cell malformedDict, intV 8 ]) -- [B5][B8]
      ,
    mkCase "ok/hit/n4-eq" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) -- [B5][B6]
      ,
    mkCase "ok/hit/n4-near" (#[ .slice (mkSlice 4 5), dictSlice4, intV 4 ]) -- [B5][B6]
      ,
    mkCase "ok/hit/n4-high" (#[ .slice (mkSlice 4 9), dictSlice4, intV 4 ]) -- [B5][B6]
      ,
    mkCase "ok/miss/n4-empty" (#[ .slice (mkSlice 4 15), dictNull, intV 4 ]) -- [B7]
      ,
    mkCase "ok/miss/n4-above" (#[ .slice (mkSlice 4 15), dictSlice4, intV 4 ]) -- [B7]
      ,
    mkCase "ok/hit/n8-eq" (#[ .slice (mkSlice 8 128), dictSlice8, intV 8 ]) -- [B5][B6]
      ,
    mkCase "ok/hit/n8-near" (#[ .slice (mkSlice 8 129), dictSlice8, intV 8 ]) -- [B5][B6]
      ,
    mkCase "ok/miss/n8-above" (#[ .slice (mkSlice 8 255), dictSlice8, intV 8 ]) -- [B7]
      ,
    mkCase "ok/hit/n0" (#[ .slice (mkSlice 0 0), dictSlice0, intV 0 ]) -- [B5][B6]
      ,
    mkCase "err/zero-key-too-long" (#[ .slice (mkSlice 4 2), dictSlice0, intV 0 ]) -- [B4]
      ,
    mkCase "ok/dict-empty-miss" (#[ .slice (mkSlice 4 7), dictNull, intV 4 ]) -- [B7]
      ,
    mkCaseCode "ok/code/f474" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) rawF474 -- [B3]
      ,
    mkCaseCode "ok/code/f475" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) rawF475 -- [B3]
      ,
    mkCaseCode "ok/code/f476" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) rawF476 -- [B3]
      ,
    mkCaseCode "ok/code/f477" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) rawF477 -- [B3]
      ,
    mkCaseCode "ok/code/f47f" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) rawF47F -- [B3]
      ,
    mkCaseCode "err/code/raw-truncated" (#[ .slice (mkSlice 4 0), dictSlice4, intV 4 ]) rawF47Trunc8 -- [B3]
      ,
    mkCase "gas/base-miss-exact" (#[ .slice (mkSlice 8 255), dictNull, intV 8 ])
      (#[ .pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr ])
      (oracleGasLimitsExact exactGas), -- [B7][B9]
    mkCase "gas/base-miss-minus-one" (#[ .slice (mkSlice 8 255), dictNull, intV 8 ])
      (#[ .pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr ])
      (oracleGasLimitsExact exactGasMinusOne), -- [B7][B9]
    mkCase "gas/hit-exact" (#[ .slice (mkSlice 4 2), dictSlice4, intV 4 ])
      (#[ .pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr ])
      (oracleGasLimitsExact hitGas), -- [B6][B9]
    mkCase "gas/hit-minus-one" (#[ .slice (mkSlice 4 2), dictSlice4, intV 4 ])
      (#[ .pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr ])
      (oracleGasLimitsExact hitGasMinusOne) -- [B6][B9]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictGetNextEqFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTGETNEXTEQ
