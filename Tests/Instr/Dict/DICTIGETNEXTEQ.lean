import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETNEXTEQ

/-!
INSTRUCTION: DICTIGETNEXTEQ

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch:
   - `execInstrDictDictGetNear` handles `.dictGetNear 9` and defers other opcodes to `next`.

2. [B2] Runtime preamble:
   - `checkUnderflow 3` requires three stack items.
   - `n` is validated by `popNatUpTo 257` (type/range checks).
   - Dictionary argument must be `.null` or `.cell`; other values fail with `typeChk`.
   - Integer key must be finite (`popIntFinite`): non-int is `typeChk`, NaN is `intOv`.

3. [B3] Integer-key conversion:
   - This concrete opcode has fixed `allowEq = true`, `goUp = true`, `intKey = true`, `unsigned = false`.
   - For signed in-range keys (`dictKeyBits?` some), runtime uses `dictNearestWithCells`.
   - Out-of-range keys branch to fallback logic.

4. [B4] `dictNearest` branches for in-range keys:
   - nearest hit -> push `(value, key-int, -1)`.
   - nearest miss -> push `0`.
   - dictionary traversal errors propagate.

5. [B5] Out-of-range negative int keys:
   - For `allowEq=true, goUp=true`, negative out-of-range uses `dictMinMaxWithCells` with `fetchMax=false` (`min`).
   - Non-empty dictionary may return hit, empty dictionary misses.
   - Dictionary traversal errors propagate.

6. [B6] Out-of-range positive int keys:
   - `cond = (key ≥ 0) != true` is false, so returns `0` directly (no dict traversal).

7. [B7] Assembler encoding/decoding:
   - `Instr.dictGetNear 9` assembles to `0xF479`.
   - `.dictGetNear args4` rejects args4 `<4` or `>15`.
   - Decoder maps `0xF474..0xF480` by `args4 = w16 &&& 0xF`.
   - Truncated/non-decodable prefixes fail decode with `invOpcode`.

8. [B8] Gas accounting:
   - Exact base gas (and exact-1 failure) must match oracle.
   - For DICTIGETNEXTEQ no extra `cellCreateGasPrice` penalty exists in the success path (it is int-key mode only).

TOTAL BRANCHES: 8

Each oracle test below is tagged [Bn] to branch(s) it covers.
Any branch not covered by oracle tests is covered by fuzz generation.
-/

private def suiteId : InstrId :=
  { name := "DICTIGETNEXTEQ" }

private def instr : Instr := .dictGetNear 9

private def dispatchSentinel : Int := 9077

private def valueA : Slice := mkSliceFromBits (natToBits 0xA5 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xE5 8)
private def valueF : Slice := mkSliceFromBits (natToBits 0xF6 8)

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]
private def dictNull : Value := .null

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
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
    | none => panic! s!"{label}: empty dict construction"

private def dict8A : Value :=
  .cell <| mkDictSetSliceRoot! "dict8A" 8 #[
    (-100, valueA), ( -128, valueB), (-1, valueC), (5, valueD), (120, valueE)
  ]

private def dict8B : Value :=
  .cell <| mkDictSetSliceRoot! "dict8B" 8 #[
    (-64, valueF), (0, valueA), (7, valueB), (9, valueC)
  ]

private def dict8C : Value :=
  .cell <| mkDictSetSliceRoot! "dict8C" 8 #[
    (-128, valueA), (127, valueB)
  ]

private def dict257A : Value :=
  .cell <| mkDictSetSliceRoot! "dict257A" 257 #[
    (0, valueA), (1, valueB), (-1, valueC)
  ]

private def dict257B : Value :=
  .cell <| mkDictSetSliceRoot! "dict257B" 257 #[
    (minInt257, valueD), (1, valueE), (maxInt257, valueF)
  ]

private def rawOpcode (w16 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w16 16) #[]

private def rawF478 : Cell := rawOpcode 0xF478
private def rawF479 : Cell := rawOpcode 0xF479
private def rawF47A : Cell := rawOpcode 0xF47A
private def rawF47B : Cell := rawOpcode 0xF47B
private def rawF47F : Cell := rawOpcode 0xF47F
private def rawF47Trunc8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def exactGas : Int := computeExactGasBudget instr
private def exactGasMinusOne : Int := computeExactGasBudgetMinusOne instr

private def mkStack (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[intV key, dict, intV n]

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

def genDictIGetNextEqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/underflow/one" (#[dict8A]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/underflow/two" (mkStack 5 dict8A 8), rng1)
    else if shape = 3 then
      (mkCase "fuzz/err/n-type" (#[(intV 5), dict8A, .slice valueA]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/err/n-range-negative" (mkStack 5 dict8A (-1)), rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/n-range-too-large" (mkStack 5 dict8A 258), rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/dict-type" (mkStack 5 (.tuple #[] ) 8), rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/key-type" (#[(.tuple #[]), dict8A, intV 8]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/key-nan" (#[.null, dict8A, intV 8]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit-8" (mkStack 5 dict8A 8), rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/hit-next-8" (mkStack 6 dict8B 8), rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/miss-8" (mkStack 127 dict8B 8), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss-narrow-empty" (mkStack 5 dictNull 8), rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/oob-positive-8" (mkStack 128 dict8A 8), rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/oob-negative-8-hit" (mkStack (-129) dict8C 8), rng1)
    else if shape = 15 then
      (mkCase "fuzz/ok/oob-negative-8-empty" (mkStack (-129) dictNull 8), rng1)
    else if shape = 16 then
      (mkCase "fuzz/ok/oob-positive-257" (mkStack (maxInt257 + 1) dict257A 257), rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/oob-negative-257-hit" (mkStack (minInt257 - 1) dict257B 257), rng1)
    else if shape = 18 then
      (mkCase "fuzz/ok/hit-257" (mkStack (-1) dict257B 257), rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/malformed-nearest" (mkStack 5 (.cell malformedDict) 8), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/malformed-minmax" (mkStack (-129) (.cell malformedDict) 8), rng1)
    else if shape = 21 then
      (mkCase
        "fuzz/gas/exact"
        (mkStack 5 dict8A 8)
        (program := #[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
        (gasLimits := oracleGasLimitsExact exactGas), rng1)
    else
      (mkCase
        "fuzz/gas/exact-minus-one"
        (mkStack 5 dict8A 8)
        (program := #[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (gasLimits := oracleGasLimitsExact exactGasMinusOne), rng1)
  let (name', rng3) := addSuffixToCaseName case0.name rng2
  ({ case0 with name := name' }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := mkStack 7 (dict8A) 8
        let expected := stack.push (intV dispatchSentinel)
        expectOkStack "dispatch/fallback" (runDispatchFallback stack) expected
    },
    { name := "unit/opcode/assemble-exact" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF479 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF479 encoding, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTIGETNEXTEQ failed: {reprStr e}")
    },
    { name := "unit/opcode/assemble-reject-low" -- [B7]
      run := do
        match assembleCp0 [Instr.dictGetNear 3] with
        | .ok _ =>
            throw (IO.userError "assemble accepted args4=3, expected rangeChk")
        | .error _ =>
            pure ()
    },
    { name := "unit/opcode/assemble-reject-high" -- [B7]
      run := do
        match assembleCp0 [Instr.dictGetNear 16] with
        | .ok _ =>
            throw (IO.userError "assemble accepted args4=16, expected rangeChk")
        | .error _ =>
            pure ()
    },
    { name := "unit/direct/hit" -- [B4][B6]
      run := do
        expectOkStack "direct/hit" (runDirect (mkStack 5 dict8A 8))
          #[.slice valueD, intV 5, intV (-1)]
    },
    { name := "unit/direct/miss/nearest-empty" -- [B4][B7]
      run := do
        expectOkStack "direct/miss/near-empty" (runDirect (mkStack 127 dict8A 8))
          #[intV 0]
    },
    { name := "unit/direct/miss/oob-positive" -- [B6]
      run := do
        expectOkStack "direct/miss/oob-positive" (runDirect (mkStack 128 dict8A 8))
          #[intV 0]
    },
    { name := "unit/direct/minmax-oob-negative" -- [B5]
      run := do
        expectOkStack "direct/minmax-oob-negative" (runDirect (mkStack (-129) dict8C 8))
          #[.slice valueA, intV (-128), intV (-1)]
    },
    { name := "unit/direct/underflow" -- [B2]
      run := do
        expectErr "direct/underflow-empty" (runDirect #[]) .stkUnd
    },
    { name := "unit/direct/err/n-type" -- [B3]
      run := do
        expectErr "direct/err/n-type" (runDirect (#[intV 5, dict8A, .tuple #[]])) .typeChk
    },
    { name := "unit/direct/err/key-type" -- [B3][B5]
      run := do
        expectErr "direct/err/key-type" (runDirect (#[.tuple #[], dict8A, intV 8])) .typeChk
    },
    { name := "unit/decode/neighbors-and-tail" -- [B7]
      run := do
        let s0 : Slice :=
          Slice.ofCell <| Cell.mkOrdinary
            (rawF478.bits ++ rawF479.bits ++ rawF47A.bits ++ rawF47B.bits ++ rawF47F.bits) #[]
        let s1 ← expectDecodeStep "decode/f478" s0 (.dictGetNear 8) 16
        let s2 ← expectDecodeStep "decode/f479" s1 (.dictGetNear 9) 16
        let s3 ← expectDecodeStep "decode/f47a" s2 (.dictGetNear 10) 16
        let s4 ← expectDecodeStep "decode/f47b" s3 (.dictGetNear 11) 16
        let s5 ← expectDecodeStep "decode/f47f" s4 (.dictGetNear 15) 16
        if s5.bitsRemaining + s5.refsRemaining != 0 then
          throw (IO.userError "decode chain did not consume full stream")
        match decodeCp0WithBits (Slice.ofCell rawF47Trunc8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated prefix")
    }
  ]
  oracle := #[
    mkCase "ok/hit/8/exact-5" (mkStack 5 dict8A 8), -- [B4][B6]
    mkCase "ok/hit/8/exact-127" (mkStack 127 dict8C 8), -- [B4][B6]
    mkCase "ok/hit/8/next-6" (mkStack 6 dict8A 8), -- [B4][B6]
    mkCase "ok/hit/8/next-3" (mkStack 3 dict8A 8), -- [B4][B6]
    mkCase "ok/hit/8/near-9" (mkStack 9 dict8B 8), -- [B4][B6]
    mkCase "ok/hit/8/near-64" (mkStack 64 dict8B 8), -- [B4][B6]
    mkCase "ok/hit/257/minus-one" (mkStack (-1) dict257A 257), -- [B4][B6]
    mkCase "ok/hit/257/max" (mkStack (maxInt257) dict257B 257), -- [B4][B6]
    mkCase "ok/miss/8/near-hi" (mkStack 126 dict8A 8), -- [B4][B7]
    mkCase "ok/miss/8/empty" (mkStack 5 dictNull 8), -- [B4][B7]
    mkCase "ok/miss/257/empty" (mkStack 5 dictNull 257), -- [B4][B7]
    mkCase "ok/miss/257/above" (mkStack 2 dict257A 257), -- [B4][B7]
    mkCase "ok/oob-pos/8/128" (mkStack 128 dict8A 8), -- [B6]
    mkCase "ok/oob-pos/8/129" (mkStack 129 dict8A 8), -- [B6]
    mkCase "ok/oob-pos/257" (mkStack (maxInt257 + 1) dict257A 257), -- [B6]
    mkCase "ok/oob-neg/8" (mkStack (-129) dict8C 8), -- [B5]
    mkCase "ok/oob-neg/8-alt" (mkStack (-129) dict8A 8), -- [B5]
    mkCase "ok/oob-neg/empty" (mkStack (-129) dictNull 8), -- [B5]
    mkCase "ok/oob-neg/257" (mkStack (minInt257 - 1) dict257B 257), -- [B5]
    mkCase "ok/oob-neg/257-empty" (mkStack (minInt257 - 1) dictNull 257), -- [B5]
    mkCase "err/underflow/empty" #[], -- [B2]
    mkCase "err/underflow/one" (#[intV 5]), -- [B2]
    mkCase "err/underflow/two" ((mkStack 5 dict8A 8).take 2), -- [B2]
    mkCase "err/n/type" (#[intV 5, dict8A, .tuple #[]]), -- [B3]
    mkCase "err/n/nan" (#[(intV 5), dict8A, .int .nan]), -- [B3]
    mkCase "err/n/negative" (mkStack 5 dict8A (-1)), -- [B3]
    mkCase "err/n/too-large" (mkStack 5 dict8A 258), -- [B3]
    mkCase "err/dict/type" (mkStack 5 (.tuple #[]) 8), -- [B4]
    mkCase "err/dict/type-cellless" (mkStack 5 (.int (.num 0)) 8), -- [B4]
    mkCase "err/key/type" (mkStack 5 dict8A 8 |>.set! 0 (.slice valueA)), -- [B5]
    mkCase "err/key/nan" (mkStack 5 dict8A 8 |>.set! 0 (.int .nan)), -- [B5]
    mkCase "err/dict-malformed-nearest" (mkStack 0 (.cell malformedDict) 8), -- [B6]
    mkCase "err/dict-malformed-minmax" (mkStack (-129) (.cell malformedDict) 8), -- [B6]
    mkCaseCode "ok/code/raw-f478" (mkStack 5 dict8A 8) rawF478, -- [B7]
    mkCaseCode "ok/code/raw-f479" (mkStack 6 dict8A 8) rawF479, -- [B7]
    mkCaseCode "ok/code/raw-f47a" (mkStack 7 dict8B 8) rawF47A, -- [B7]
    mkCaseCode "ok/code/raw-f47b" (mkStack (-1) dict8B 8) rawF47B, -- [B7]
    mkCaseCode "ok/code/raw-f47f" (mkStack 5 dict8A 8) rawF47F, -- [B7]
    mkCaseCode "err/code/raw/trunc8" #[] rawF47Trunc8, -- [B7]
    mkCase "gas/exact" (mkStack 5 dict8A 8)
      #[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact exactGas), -- [B8]
    mkCase "gas/exact-minus-one" (mkStack 5 dict8A 8)
      #[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact exactGasMinusOne) -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictIGetNextEqFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETNEXTEQ
