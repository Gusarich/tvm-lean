import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.ONLYX

/-
INSTRUCTION: ONLYX

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Normal execution, `x == depth`: exact keep of all `x` elements means no stack truncation.
2. [B2] Normal execution, `0 < x < depth`: stack is truncated to exactly the bottom `x` elements.
3. [B3] Normal execution, `x == 0`: all stack items are dropped.
4. [B4] Error path, empty stack: `popNatUpTo` raises `.stkUnd`.
5. [B5] Error path, `x > depth`: after successful `popNatUpTo`, compare fails and raises `.stkUnd`.
6. [B6] Error path, top is not `Int`: `popInt` raises `.typeChk`.
7. [B7] Error path, top `Int` negative: `popNatUpTo` raises `.rangeChk`.
8. [B8] Error path, top `Int` > `1<<30-1`: `popNatUpTo` raises `.rangeChk`.
9. [B9] Error path, top is `Int.nan`: `popNatUpTo` raises `.rangeChk`.
10. [B10] Assembler encoding behavior is fixed-width and argument-free:
    `.onlyX` always encodes as fixed 8-bit opcode `0x6b`; there is no operand-range branch.
11. [B11] Decoder behavior / round-trip boundary:
    decoding `0x6b` must produce `.onlyX` (encode/decode identity in round-trip checks),
    while adjacent opcode `0x6a` must remain `.onlyTopX` (no aliasing).
12. [B12] Gas accounting:
    Lean/C++ only consume base fixed gas (`computeExactGasBudget .onlyX`), no variable penalty;
    exact gas succeeds and exact-minus-one must fail with out-of-gas.

TOTAL BRANCHES: 12

Every branch from above is covered by at least one oracle case in this file.
-/

private def onlyXId : InstrId := { name := "ONLYX" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.onlyX])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := onlyXId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def onlyXGasExact : Int :=
  computeExactGasBudget .onlyX

private def onlyXGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .onlyX

private def mkStackWithTop (below : Nat) (top : Value) : Array Value :=
  Id.run do
    let mut st : Array Value := #[]
    for i in [0:below] do
      st := st.push (intV (Int.ofNat (i + 1)))
    return st.push top

private def genOnlyXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (below, rng2) := randNat rng1 0 8
    let (xNat, rng3) := randNat rng2 0 (below + 1)
    (mkCase s!"fuzz/success/{shape}" (mkStackWithTop below (intV (Int.ofNat xNat))), rng3)
  else if shape = 1 then
    let (below, rng2) := randNat rng1 0 8
    let x : Int := Int.ofNat (below + 1)
    (mkCase s!"fuzz/noop/{shape}" (mkStackWithTop below (intV x)), rng2)
  else if shape = 2 then
    let (below, rng2) := randNat rng1 0 6
    let (delta, rng3) := randNat rng2 1 4
    let x : Int := Int.ofNat ((below + 1) + delta)
    (mkCase s!"fuzz/underflow/{shape}" (mkStackWithTop below (intV x)), rng3)
  else if shape = 3 then
    let (below, rng2) := randNat rng1 0 8
    let (negAbs, rng3) := randNat rng2 1 64
    (mkCase s!"fuzz/negative/{shape}" (mkStackWithTop below (intV (-Int.ofNat negAbs))), rng3)
  else if shape = 4 then
    let (below, rng2) := randNat rng1 0 8
    let (delta, rng3) := randNat rng2 0 255
    let x : Int := Int.ofNat ((1 <<< 30) + delta)
    (mkCase s!"fuzz/range-max/{shape}" (mkStackWithTop below (intV x)), rng3)
  else if shape = 5 then
    let (below, rng2) := randNat rng1 0 8
    (mkCase s!"fuzz/nan/{shape}" (mkStackWithTop below (.int .nan)), rng2)
  else if shape = 6 then
    let (below, rng2) := randNat rng1 0 8
    (mkCase s!"fuzz/type/null/{shape}" (mkStackWithTop below .null), rng2)
  else if shape = 7 then
    let (below, rng2) := randNat rng1 0 8
    (mkCase s!"fuzz/type/cell/{shape}" (mkStackWithTop below (.cell Cell.empty)), rng2)
  else if shape = 8 then
    (mkCase "fuzz/empty-stack" #[], rng1)
  else
    let (below, rng2) := randNat rng1 0 8
    let (x, rng3) := pickInt257Boundary rng2
    let topVals : Array Value := mkStackWithTop below (intV x)
    (mkCase "fuzz/mixed-boundary" topVals, rng3)

def suite : InstrSuite where
  id := onlyXId
  unit := #[
    { name := "unit/asm/onlyx-encodes-6b"
      run := do
        let code ←
          match assembleCp0 [Instr.onlyX] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assembleCp0 onlyX failed: {e}")
        match decodeCp0WithBits (Slice.ofCell code) with
        | .error e => throw (IO.userError s!"decodeCp0WithBits onlyX failed: {e}")
        | .ok (instr, bits, _) =>
            if instr != Instr.onlyX || bits ≠ 8 then
              throw (IO.userError s!"decode unexpected: instr={reprStr instr} bits={bits}")
            pure ()
    },
    { name := "unit/asm/onlyx-decode-roundtrip"
      run := do
        let code1 ←
          match assembleCp0 [Instr.onlyX] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assembleCp0 onlyX failed: {e}")
        match decodeCp0WithBits (Slice.ofCell code1) with
        | .error e => throw (IO.userError s!"decodeCp0WithBits onlyX failed: {e}")
        | .ok (decoded, _, _) =>
            let code2 ←
              match assembleCp0 [decoded] with
              | .ok c => pure c
              | .error e => throw (IO.userError s!"re-assemble decoded opcode failed: {e}")
            if code1 != code2 then
              throw (IO.userError "decode/encode roundtrip mismatch for ONLYX")
            pure ()
    },
    { name := "unit/asm/onlyx-0x6a-neighbor-distinct"
      run := do
        let onlyXCode ←
          match assembleCp0 [Instr.onlyX] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assembleCp0 onlyX failed: {e}")
        let onlyTopXCode ←
          match assembleCp0 [Instr.onlyTopX] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assembleCp0 onlyTopX failed: {e}")
        match decodeCp0WithBits (Slice.ofCell onlyXCode), decodeCp0WithBits (Slice.ofCell onlyTopXCode) with
        | .ok (instrX, _, _), .ok (instrTop, _, _) =>
            if instrX == instrTop then
              throw (IO.userError "0x6b and 0x6a decoded to same instruction")
            if instrX != Instr.onlyX || instrTop != Instr.onlyTopX then
              throw (IO.userError "adjacent decode mismatch for ONLYX / ONLYTOPX")
            pure ()
        | .error e, _ => throw (IO.userError s!"decode onlyX side failed: {e}")
        | _, .error e => throw (IO.userError s!"decode onlyTopX side failed: {e}")
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "ok/noop/depth-1" #[intV 1],
    -- [B1]
    mkCase "ok/noop/depth-2" #[intV 7, intV 2],
    -- [B1]
    mkCase "ok/noop/depth-3" #[intV 11, intV 22, intV 3],
    -- [B1]
    mkCase "ok/noop/depth-4" #[intV 11, intV 22, intV 33, intV 4],
    -- [B1]
    mkCase "ok/noop/depth-5-mixed-bottom" #[.cell Cell.empty, intV 55, .null, .int (.num 999), intV 5],

    -- [B2]
    mkCase "ok/drop/depth-3-keep-2" #[intV 1, intV 2, intV 2],
    -- [B2]
    mkCase "ok/drop/depth-4-keep-1" #[intV 1, .cell Cell.empty, intV 3, intV 1],
    -- [B2]
    mkCase "ok/drop/depth-5-keep-3" #[intV 10, intV 20, intV 30, intV 40, intV 3],
    -- [B2]
    mkCase "ok/drop/depth-6-keep-2" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 2],
    -- [B2]
    mkCase "ok/drop/depth-3-cell-bottom" #[intV 7, .cell Cell.empty, intV 2],
    -- [B2]
    mkCase "ok/drop/depth-4-null-bottom" #[intV 9, .null, .int (.num 8), intV 1],

    -- [B3]
    mkCase "ok/zero/depth-1" #[intV 0],
    -- [B3]
    mkCase "ok/zero/depth-2" #[intV 11, intV 0],
    -- [B3]
    mkCase "ok/zero/depth-4" #[intV 11, .cell Cell.empty, .null, intV 0],
    -- [B3]
    mkCase "ok/zero/depth-5" #[intV 1, intV 2, intV 3, intV 4, intV 0],

    -- [B4]
    mkCase "error/underflow/empty" #[],

    -- [B5]
    mkCase "error/underflow/depth-2" #[intV 1, intV 3],
    -- [B5]
    mkCase "error/underflow/depth-4" #[intV 10, intV 20, intV 30, intV 9],

    -- [B6]
    mkCase "error/type/top-null" #[.null],
    -- [B6]
    mkCase "error/type/top-cell" #[.cell Cell.empty],
    -- [B6]
    mkCase "error/type/top-builder" #[.builder Builder.empty],
    -- [B6]
    mkCase "error/type/top-quit0" #[.cont (.quit 0)],

    -- [B7]
    mkCase "error/range/negative-one" #[intV (-1), intV 10],
    -- [B7]
    mkCase "error/range/negative-large" #[intV (-987654321)],

    -- [B8]
    mkCase "error/range/overflow-max-plus-1" #[intV (Int.ofNat (1 <<< 30) ), intV 1],
    -- [B8]
    mkCase "error/range/overflow-large" #[intV (Int.ofNat ((1 <<< 30) + 99)), intV 1],

    -- [B9]
    mkCase "error/range/nan" #[.int .nan],

    -- [B10]
    mkCase "gas/exact-success" #[intV 9, intV 2]
      #[.pushInt (.num onlyXGasExact), .tonEnvOp .setGasLimit, .onlyX],
    -- [B10]
    mkCase "gas/exact-minus-one-oog" #[intV 9, intV 2]
      #[.pushInt (.num onlyXGasExactMinusOne), .tonEnvOp .setGasLimit, .onlyX],

    -- [B11]
    mkCase "decode/noise-neighbor-onlytopx-distinct" #[intV 8, intV 1]
      #[.onlyTopX],
    -- [B11]
    mkCase "decode/roundtrip-canonical" #[intV 8, intV 2]
      #[.onlyX]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 500
      gen := genOnlyXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.ONLYX
