import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.ROLL

/-!
BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Normal transform path
   - Precondition: stack has at least one cell for pop + parsed `x` is in `[0, stack.size - 1]` and valid range.
   - Behavior: rotate value at stack index `x` (from top) to top by adjacent swaps.
   - Stack result categories:
     - `x = 0` is a no-op in result order.
     - `x > 0` moves the selected element up by `x` swaps.
2. [B2] Input pop/type/range validation in `popNatUpTo` for `x`
   - Empty stack after `checkUnderflow(1)` equivalent => `.stkUnd`.
   - Top not integer => `.typeChk`.
   - Top is non-finite integer (`NaN`) => `.rangeChk`.
   - Top integer below 0 => `.rangeChk`.
   - Top integer greater than `(1 << 30) - 1` => `.rangeChk`.
3. [B3] Post-pop depth validation (`x < stack.size`)
   - If `x` is not strictly less than stack depth => `.stkUnd`.
   - Otherwise proceed to swap loop.
4. [B4] Variable gas branch on `x`
   - `x <= 255`: no extra gas beyond base per-instruction cost.
   - `x > 255`: extra gas `x - 255`.
5. [B5] Gas outcome edges
   - exact-base budget success.
   - exact-base-minus-one failure.
   - exact-with-penalty success (`x > 255`).
   - exact-with-penalty-minus-one failure (`x > 255`).
6. [B6] Assembler encoding
   - No operands/params for `ROLL`; valid encoding is unique fixed opcode 0x61 (8 bits).
   - No out-of-range parameter branch exists because instruction has no immediate argument in Lean/C++ assembly mapping.
7. [B7] Decoder behavior
   - Exact decode of opcode `0x61` maps to `.roll`.
   - Adjacent opcodes are distinct: `0x60` => `.pick`, `0x62` => `.rollrev`.
   - Truncated/invalid byte prefixes should decode as `.invOpcode` (C++ equivalent).

TOTAL BRANCHES: 7
-
  The branch map intentionally separates gas and decode/assemble behavior even where Lean
  implementation is structurally compact, because those branches are externally visible and
  testable in oracle/runtime behavior.
-/

private def rollId : InstrId := { name := "ROLL" }
private def rollInstr : Instr := .roll

private def rollMaxOffset : Nat := (1 <<< 30) - 1
private def rollMaxOffsetInt : Int := Int.ofNat rollMaxOffset
private def rollOverMaxOffsetInt : Int := Int.ofNat ((1 <<< 30))

private def rawRoll : Cell := Cell.mkOrdinary (natToBits 0x61 8) #[]
private def rawPick : Cell := Cell.mkOrdinary (natToBits 0x60 8) #[]
private def rawRollRev : Cell := Cell.mkOrdinary (natToBits 0x62 8) #[]
private def rawUnknown8 : Cell := Cell.mkOrdinary (natToBits 0xFF 8) #[]
private def rawTrunc4 : Cell := Cell.mkOrdinary (natToBits 0x6 4) #[]

private def dispatchSentinel : Int := 49125

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def mkRollStack (x : Nat) : Array Value :=
  Id.run do
    let mut st : Array Value := #[]
    for i in [0 : x + 1] do
      st := st.push (intV (Int.ofNat i))
    pure st

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rollId
    program := #[rollInstr]
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
    instr := rollId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def rollBaseGas : Int :=
  computeExactGasBudget rollInstr

private def rollGasForOffset (x : Nat) : Int :=
  if x ≤ 255 then
    rollBaseGas
  else
    rollBaseGas + Int.ofNat (x - 255)

private def gasExact (x : Nat) : OracleGasLimits :=
  oracleGasLimitsExact (rollGasForOffset x)

private def gasExactMinusOne (x : Nat) : OracleGasLimits :=
  oracleGasLimitsExact (let b := rollGasForOffset x; if b > 0 then b - 1 else 0)

private def mkGasCaseExact
    (name : String)
    (x : Nat)
    (stack : Array Value := mkRollStack x)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rollId
    program := #[.pushInt (.num (rollGasForOffset x)), .tonEnvOp .setGasLimit, rollInstr]
    initStack := stack
    gasLimits := gasExact x
    fuel := fuel }

private def mkGasCaseMinusOne
    (name : String)
    (x : Nat)
    (stack : Array Value := mkRollStack x)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rollId
    program := #[.pushInt (.num (rollGasForOffset x)), .tonEnvOp .setGasLimit, rollInstr]
    initStack := stack
    gasLimits := gasExactMinusOne x
    fuel := fuel }

private def runRollDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackRoll rollInstr stack

private def runRollDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackRoll instr (VM.push (intV dispatchSentinel)) stack

private def rollFuzzBoundaryPool : Array Nat :=
  #[
    0, 1, 2, 3, 4, 5, 7, 16, 63, 127, 128, 129, 255, 256, 257, 300, 301
  ]

private def genRollFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (baseCase, rng2) :=
    match shape with
    | 0 =>
      let (x, rng') := pickFromPool rollFuzzBoundaryPool rng1
      (mkCase (s!"fuzz/ok/boundary/x-{x}") (mkRollStack x), rng')
    | 1 =>
      let (x, rng') := randNat rng1 0 4
      (mkCase (s!"fuzz/ok/random-small/x-{x}") (mkRollStack x), rng')
    | 2 =>
      let (x, rng') := randNat rng1 0 16
      (mkCase (s!"fuzz/ok/minimal-stack/x-{x}") (mkRollStack (x + 1)), rng')
    | 3 =>
      (mkCodeCase "fuzz/ok/raw/opcode-roll" (mkRollStack 1) rawRoll, rng1)
    | 4 =>
      (mkCodeCase "fuzz/ok/raw/opcode-rollrev-is-distinct" (mkRollStack 1) rawRollRev, rng1)
    | 5 =>
      (mkCodeCase "fuzz/ok/raw/opcode-pick-is-distinct" (mkRollStack 1) rawPick, rng1)
    | 6 =>
      let (x, rng') := pickFromPool rollFuzzBoundaryPool rng1
      let base := mkRollStack x
      (mkGasCaseExact (s!"fuzz/gas/exact/offset-{x}") x base, rng')
    | 7 =>
      let (x, rng') := pickFromPool rollFuzzBoundaryPool rng1
      (mkGasCaseMinusOne (s!"fuzz/gas/exact-minus-one/offset-{x}") x (mkRollStack x), rng')
    | 8 =>
      (mkCodeCase "fuzz/err/raw/opcode-unknown8" #[] rawUnknown8, rng1)
    | 9 =>
      (mkCodeCase "fuzz/err/raw/opcode-trunc4" #[] rawTrunc4, rng1)
    | 10 =>
      (mkCase "fuzz/err/empty-stack" #[], rng1)
    | 11 =>
      (mkCase "fuzz/err/type-top-null" #[.null, intV 7], rng1)
    | 12 =>
      (mkCase "fuzz/err/type-top-cont" #[.cont (.quit 0), intV 7], rng1)
    | 13 =>
      (mkCase "fuzz/err/range-top-nan" #[.int .nan, intV 7], rng1)
    | 14 =>
      (mkCase "fuzz/err/range-top-negative" #[intV (-1), intV 7], rng1)
    | 15 =>
      (mkCase "fuzz/err/range-top-over-max" #[intV rollOverMaxOffsetInt, intV 7], rng1)
    | 16 =>
      (mkCase "fuzz/err/size-underflow-eq-size" #[intV 2, intV 7], rng1)
    | 17 =>
      (mkCase "fuzz/err/size-underflow-greater" #[intV 5, intV 7], rng1)
    | 18 =>
      (mkGasCaseExact "fuzz/type/top-with-gas-tight" 1 #[.null, intV 7], rng1)
    | _ =>
      let (x, rng') := randNat rng1 0 128
      (mkCase (s!"fuzz/ok/smoke-noise/x-{x}") (mkRollStack x), rng')
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

private def rollOracleCases : Array OracleCase := #[
  -- [B1]: success with direct roll semantics.
  mkCase "ok/roll/x0-no-op" (mkRollStack 0), -- [B1]
  mkCase "ok/roll/x1-1-step" (mkRollStack 1), -- [B1]
  mkCase "ok/roll/x2-2-step" (mkRollStack 2), -- [B1]
  mkCase "ok/roll/x3" (mkRollStack 3), -- [B1]
  mkCase "ok/roll/x7" (mkRollStack 7), -- [B1]
  mkCase "ok/roll/x63" (mkRollStack 63), -- [B1]
  mkCase "ok/roll/x127" (mkRollStack 127), -- [B1]
  mkCase "ok/roll/x255-edge-no-penalty" (mkRollStack 255), -- [B1][B4]
  mkCase "ok/roll/x256-edge-penalty" (mkRollStack 256), -- [B1][B4]
  mkCase "ok/roll/x257" (mkRollStack 257), -- [B1][B4]
  mkCase "ok/roll/x300-large" (mkRollStack 300), -- [B1][B4]

  -- [B2]: pre-swap range/type validation for `x`.
  mkCase "err/empty/underflow-before-pop" #[], -- [B2]
  mkCase "err/type-top-null" #[.null], -- [B2]
  mkCase "err/type-top-cell" #[.cell Cell.empty], -- [B2]
  mkCase "err/range-top-nan" #[(.int .nan)], -- [B2]
  mkCase "err/range-top-negative" #[intV (-1)], -- [B2]
  mkCase "err/range-top-over-max" #[intV rollOverMaxOffsetInt], -- [B2]

  -- [B3]: depth guard after parsing x (`x < size`).
  mkCase "err/underflow-x-ge-size-1" #[intV 1], -- [B3]
  mkCase "err/underflow-x-ge-size-2" #[intV 2, intV 6], -- [B3]
  mkCase "err/underflow-x-eq-size" (mkRollStack 3), -- [B3]

  -- [B4] and [B5]: gas edges.
  mkGasCaseExact "gas/exact/base" 7 (mkRollStack 7), -- [B4][B5]
  mkGasCaseMinusOne "gas/exact-minus-one/base" 7 (mkRollStack 7), -- [B4][B5]
  mkGasCaseExact "gas/exact/edge-255-no-penalty" 255 (mkRollStack 255), -- [B4][B5]
  mkGasCaseMinusOne "gas/exact-minus-one/edge-255" 255 (mkRollStack 255), -- [B4][B5]
  mkGasCaseExact "gas/exact/edge-256-penalty" 256 (mkRollStack 256), -- [B4][B5]
  mkGasCaseMinusOne "gas/exact-minus-one/edge-256" 256 (mkRollStack 256), -- [B4][B5]

  -- [B6]/[B7]: assembler + opcode decode behavior and boundaries.
  mkCodeCase "decode/raw-roll-opcode" (mkRollStack 3) rawRoll, -- [B6][B7]
  mkCodeCase "decode/raw-pick-neighbor" (mkRollStack 0) rawPick, -- [B7]
  mkCodeCase "decode/raw-rollrev-neighbor" (mkRollStack 0) rawRollRev, -- [B7]
  mkCodeCase "decode/raw-unknown8-triggers-invopcode" #[] rawUnknown8, -- [B7]
  mkCodeCase "decode/raw-truncated4-triggers-invopcode" #[] rawTrunc4 -- [B7]
]

private def rollFuzzSpec : Array FuzzSpec :=
  #[{ seed := fuzzSeedForInstr rollId, count := 500, gen := genRollFuzzCase }]


def suite : InstrSuite where
  id := rollId
  unit := #[
    { name := "unit/dispatch/fallback-to-next"
      run := do
        expectOkStack "dispatch-fallback" (runRollDispatchFallback .add #[]) #[intV dispatchSentinel]
    }
  ]
  oracle := rollOracleCases
  fuzz := rollFuzzSpec

initialize registerSuite suite

end Tests.Instr.Stack.ROLL
