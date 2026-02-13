import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCHG3

/- 
INSTRUCTION: XCHG3

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime normal path — valid stack with enough depth executes three swaps in order `swap 2 x`, `swap 1 y`, `swap 0 z`.
2. [B2] Runtime underflow branch — execution requires `need = max(x,y,z,2)` and fails with `.stkUnd` when `need >= stack.size` (strict check).
3. [B3] Runtime indices semantics — no type checks and no index-order constraints in execution (`x` may be 0, duplicate indices are allowed); this is inferred from explicit `swap` operations.
4. [B4] Assembler encoding — `.xchg3 x y z` only checks `x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15`; anything above 15 causes `.rangeChk`.
5. [B5] Decoder behavior (16-bit) — 16-bit stream with 4-bit prefix `0x4` decodes to `.xchg3`.
6. [B6] Decoder behavior (24-bit alias) — 24-bit stream with 12-bit prefix `0x540` also decodes to `.xchg3`.
7. [B7] Decoder error branches — truncated bitstreams (e.g. 15-bit or 23-bit variants) do not contain a full opcode and fail with `.invOpcode`.
8. [B8] Gas accounting — fixed-gas execution (`computeExactGasBudget`) for normal 16-bit `.xchg3` form is stable after argument application.
9. [B9] Gas edge branch — exact budget succeeds; budget minus one fails with out-of-gas behavior.

TOTAL BRANCHES: 9

Each branch above is represented by the tagged tests below in `unit`, `oracle`, or `fuzz`.
-/

private def xchg3Id : InstrId :=
  { name := "XCHG3" }

private def xchg3Code16 (x y z : Nat) : Cell :=
  let args : Nat := (x <<< 8) + (y <<< 4) + z
  Cell.mkOrdinary (natToBits (0x4000 + args) 16) #[]

private def xchg3Code24 (x y z : Nat) : Cell :=
  let args : Nat := (x <<< 8) + (y <<< 4) + z
  let word24 : Nat := (0x540 <<< 12) + args
  Cell.mkOrdinary (natToBits word24 24) #[]

private def xchg3Trunc16Code : Cell :=
  Cell.mkOrdinary (natToBits 0x5fff 15) #[]

private def xchg3Trunc24Code : Cell :=
  Cell.mkOrdinary (natToBits ((0x540 <<< 12)) 23) #[]

private def xchg3Need (x y z : Nat) : Nat :=
  Nat.max (Nat.max (Nat.max x y) z) 2

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.xchg3 1 2 3])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchg3Id
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
    instr := xchg3Id
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def xchg3SetGasExact : Int :=
  computeExactGasBudget (.xchg3 1 2 3)

private def xchg3SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xchg3 1 2 3)

private def pickFuzzValue (rng0 : StdGen) : Value × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    (intV 0, rng1)
  else if mode = 1 then
    (intV 1, rng1)
  else if mode = 2 then
    (intV (-1), rng1)
  else if mode = 3 then
    let (n, rng2) := pickInt257Boundary rng1
    (intV n, rng2)
  else if mode = 4 then
    (intV maxInt257, rng1)
  else if mode = 5 then
    (intV minInt257, rng1)
  else if mode = 6 then
    (.null, rng1)
  else if mode = 7 then
    (.cell Cell.empty, rng1)
  else if mode = 8 then
    (.tuple #[], rng1)
  else
    (.cont (.quit 0), rng1)

private def randomValueStack (n : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut rng := rng0
  let mut out : Array Value := #[]
  let mut i : Nat := 0
  while i < n do
    let (v, rng') := pickFuzzValue rng
    out := out.push v
    rng := rng'
    i := i + 1
  return (out, rng)

private def genXchg3FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  if shape = 0 then
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := randNat rng2 0 15
    let (z, rng4) := randNat rng3 0 15
    let need := xchg3Need x y z
    let (extra, rng5) := randNat rng4 0 4
    let (stack, rng6) := randomValueStack (need + extra + 1) rng5
    (mkCase s!"fuzz/ok/valid/{x}_{y}_{z}_plus{extra}" stack (#[.xchg3 x y z]), rng6)
  else if shape = 1 then
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := randNat rng2 0 15
    let (z, rng4) := randNat rng3 0 15
    let need := xchg3Need x y z
    let (depth, rng5) := randNat rng4 0 need
    let (stack, rng6) := randomValueStack depth rng5
    (mkCase s!"fuzz/err/underflow/{x}_{y}_{z}_size{depth}" stack (#[.xchg3 x y z]), rng6)
  else if shape = 2 then
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := randNat rng2 0 15
    let (z, rng4) := randNat rng3 0 15
    let need := xchg3Need x y z
    let (extra, rng5) := randNat rng4 0 3
    let (stack, rng6) := randomValueStack (need + extra + 1) rng5
    (mkCaseCode s!"fuzz/raw/16/ok/{x}_{y}_{z}" stack (xchg3Code16 x y z), rng6)
  else if shape = 3 then
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := randNat rng2 0 15
    let (z, rng4) := randNat rng3 0 15
    let need := xchg3Need x y z
    let (extra, rng5) := randNat rng4 0 2
    let (stack, rng6) := randomValueStack (need + extra + 1) rng5
    (mkCaseCode s!"fuzz/raw/24/ok/{x}_{y}_{z}" stack (xchg3Code24 x y z), rng6)
  else if shape = 4 then
    let (kind, rng2) := randNat rng1 0 3
    let (stack, rng3) :=
      match kind with
      | 0 => (#[.cell Cell.empty], rng2)
      | 1 => (#[intV 7, .null], rng2)
      | 2 => (Array.replicate 3 (intV 11), rng2)
      | _ => (Array.replicate 8 (intV 1), rng2)
    (if kind = 0 then
      mkCase "fuzz/err/asm/x-too-large" stack (#[.xchg3 16 0 0])
    else if kind = 1 then
      mkCase "fuzz/err/asm/y-too-large" stack (#[.xchg3 1 16 0])
    else if kind = 2 then
      mkCase "fuzz/err/asm/z-too-large" stack (#[.xchg3 1 0 16])
    else
      mkCase "fuzz/err/asm/multi-too-large" stack (#[.xchg3 16 16 16]), rng3)
  else if shape = 5 then
    let (kind, rng2) := randNat rng1 0 1
    let (stack, rng3) := randomValueStack 2 rng2
    if kind = 0 then
      (mkCaseCode "fuzz/err/decode/truncated-15" stack xchg3Trunc16Code, rng3)
    else
      (mkCaseCode "fuzz/err/decode/truncated-23" stack xchg3Trunc24Code, rng3)
  else if shape = 6 then
    let (tight, rng2) := randNat rng1 0 1
    let budget : Int := if tight = 0 then xchg3SetGasExact else xchg3SetGasExactMinusOne
    let (stack, rng3) := randomValueStack 4 rng2
    let name := if tight = 0 then "fuzz/gas/exact" else "fuzz/gas/exact-minus-one"
    (mkCase name stack
      #[.pushInt (.num budget), .tonEnvOp .setGasLimit, .xchg3 1 2 3]
      { gasLimit := budget, gasMax := budget, gasCredit := 0 }, rng3)
  else if shape = 7 then
    let (pick, rng2) := randNat rng1 0 2
    let (x, y, z) :=
      if pick = 0 then
        (0, 0, 0)
      else if pick = 1 then
        (0, 15, 15)
      else
        (15, 15, 15)
    let need := xchg3Need x y z
    let (stack, rng3) := randomValueStack (need + 1) rng2
    (mkCase s!"fuzz/ok/boundary-args/{x}_{y}_{z}" stack (#[.xchg3 x y z]), rng3)
  else
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := randNat rng2 0 15
    let (z, rng4) := randNat rng3 0 15
    let need := xchg3Need x y z
    let (len, rng5) := randNat rng4 need (need + 6)
    let (stack, rng6) := randomValueStack len rng5
    (mkCase s!"fuzz/ok/random-depth/{x}_{y}_{z}_{len}" stack (#[.xchg3 x y z]), rng6)

def suite : InstrSuite where
  id := xchg3Id
  unit := #[]
  oracle := #[
    -- [B1,B3]
    mkCase "ok/normal/depth3-ascending" #[intV 1, intV 2, intV 3],
    -- [B1,B3]
    mkCase "ok/normal/depth3-descending" #[intV 9, intV 8, intV 7],
    -- [B1,B3]
    mkCase "ok/normal/depth3-zeros" #[intV 0, intV 0, intV 0],
    -- [B1,B3]
    mkCase "ok/normal/depth3-negative" #[intV (-1), intV 7, intV (-3)],
    -- [B1,B3]
    mkCase "ok/normal/depth3-boundary-int" #[intV maxInt257, intV 0, intV minInt257],
    -- [B1,B3]
    mkCase "ok/normal/depth4-with-tail" #[intV 10, intV 11, intV 12, intV 13],
    -- [B1,B3]
    mkCase "ok/normal/depth5-mixed" #[intV 1, .null, .cell Cell.empty, intV 42, intV 99],
    -- [B1,B3]
    mkCase "ok/normal/depth6-continuation" #[.cont (.quit 0), intV 2, intV 3, intV 4, .null, intV 5],
    -- [B1,B3]
    mkCase "ok/normal/depth7-mixed-types" #[.null, intV 0, intV 1, .cell Cell.empty, intV 2, .tuple #[], intV 3],
    -- [B1,B3]
    mkCase "ok/normal/all-null" #[.null, .null, .null],
    -- [B1,B3]
    mkCase "ok/normal/zero-arg-triplet" #[intV 7, intV 8, intV 9] (#[.xchg3 0 0 0]),
    -- [B1,B3]
    mkCase "ok/normal/low-high-args" #[intV 1, intV 2, intV 3] (#[.xchg3 0 1 15]),
    -- [B1,B3]
    mkCase "ok/normal/high-low-args" #[intV 1, intV 2, intV 3] (#[.xchg3 15 0 1]),
    -- [B1,B3]
    mkCase "ok/normal/duplicates" #[intV 5, intV 5, intV 5] (#[.xchg3 2 2 2]),
    -- [B1]
    mkCase "ok/normal/max-args" (Array.replicate 16 (intV 1)) (#[.xchg3 15 14 13]),
    -- [B1]
    mkCase "ok/normal/large-depth-tail" #[intV 100, intV 101, intV 102, intV 103, intV 104, intV 105, intV 106],
    -- [B1,B6]
    mkCaseCode "ok/raw/decode-16/basic" #[intV 1, intV 2, intV 3] (xchg3Code16 1 2 3),
    -- [B1,B5]
    mkCaseCode "ok/raw/decode-16/extreme" (Array.replicate 16 (intV 1)) (xchg3Code16 15 15 15),
    -- [B1,B6]
    mkCaseCode "ok/raw/decode-24/basic" #[intV 1, intV 2, intV 3] (xchg3Code24 0 1 2),
    -- [B1,B6]
    mkCaseCode "ok/raw/decode-24/extreme" (Array.replicate 16 (intV 7)) (xchg3Code24 15 0 15),
    -- [B1,B6]
    mkCaseCode "ok/raw/decode-24/noise-tail" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6] (xchg3Code24 7 8 9),
    -- [B2]
    mkCase "err/underflow-empty" #[],
    -- [B2]
    mkCase "err/underflow-one" #[intV 11],
    -- [B2]
    mkCase "err/underflow-two" #[intV 1, intV 2],
    -- [B2]
    mkCase "err/underflow-three" #[intV 5, intV 6, intV 7],
    -- [B2]
    mkCase "err/underflow-four" #[intV 8, intV 9, intV 10, intV 11],
    -- [B2]
    mkCase "err/underflow-boundary-eq-max" (Array.replicate 15 (intV 7)) (#[.xchg3 15 14 0]),
    -- [B2]
    mkCase "err/underflow-boundary-small" (Array.replicate 2 (intV 9)) (#[.xchg3 0 0 0]),
    -- [B4]
    mkCase "err/asm/x-too-large" (Array.replicate 3 (intV 0)) (#[.xchg3 16 0 0]),
    -- [B4]
    mkCase "err/asm/y-too-large" (Array.replicate 3 (intV 1)) (#[.xchg3 1 16 0]),
    -- [B4]
    mkCase "err/asm/z-too-large" (Array.replicate 3 (intV 2)) (#[.xchg3 1 0 16]),
    -- [B4]
    mkCase "err/asm/all-too-large" (Array.replicate 3 (intV 3)) (#[.xchg3 16 16 16]),
    -- [B7]
    mkCaseCode "err/decode/truncated-15bits" (#[intV 1]) xchg3Trunc16Code,
    -- [B7]
    mkCaseCode "err/decode/truncated-23bits" (#[intV 1, intV 2]) xchg3Trunc24Code,
    -- [B8]
    { name := "ok/gas/exact"
      instr := xchg3Id
      program := #[.pushInt (.num xchg3SetGasExact), .tonEnvOp .setGasLimit, .xchg3 2 4 1]
      initStack := #[intV 1, intV 2, intV 3, intV 4, intV 5]
      gasLimits := { gasLimit := xchg3SetGasExact, gasMax := xchg3SetGasExact, gasCredit := 0 } },
    -- [B9]
    { name := "err/gas/exact-minus-one"
      instr := xchg3Id
      program := #[.pushInt (.num xchg3SetGasExactMinusOne), .tonEnvOp .setGasLimit, .xchg3 2 4 1]
      initStack := #[intV 1, intV 2, intV 3, intV 4, intV 5]
      gasLimits := { gasLimit := xchg3SetGasExactMinusOne, gasMax := xchg3SetGasExactMinusOne, gasCredit := 0 } }
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr xchg3Id
      count := 500
      gen := genXchg3FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCHG3
