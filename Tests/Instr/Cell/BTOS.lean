import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BTOS

/-
BTOS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt .btos`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf50` decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xcf50` encode)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_int_builder_func`, BTOS wiring)

Covered oracle branches:
- underflow (`stkUnd`) on empty stack;
- type check (`typeChk`) when top is not a builder;
- success on empty builder;
- success on program-built non-empty builders (bits and refs);
- gas edge via `SETGASLIMIT` (exact vs exact-minus-one).
-/

private def btosId : InstrId := { name := "BTOS" }

private def btosInstr : Instr := .cellExt .btos

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[btosInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := btosId
    program := program
    initStack := stack
    fuel := fuel }

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA]

private def btosSetGasExact : Int :=
  computeExactGasBudget btosInstr

private def btosSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne btosInstr

private def fuzzBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def pickBitsLenMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 5 then
    let (idx, rng2) := randNat rng1 0 (fuzzBitsBoundaryPool.size - 1)
    (fuzzBitsBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 1023

private def fuzzRefPool : Array Cell :=
  #[Cell.empty, refLeafA, refLeafB]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genRefs (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut out : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (c, rng') := pickFromPool fuzzRefPool rng
    out := out.push c
    rng := rng'
  return (out, rng)

private def genBuilderMixed (rng0 : StdGen) : Builder × StdGen := Id.run do
  let (bitsLen, rng1) := pickBitsLenMixed rng0
  let (refCount, rng2) := randNat rng1 0 4
  let (bits, rng3) := randBitString bitsLen rng2
  let (refs, rng4) := genRefs refCount rng3
  return (({ bits := bits, refs := refs } : Builder), rng4)

private def fuzzNoisePool : Array Value :=
  #[.null, intV 0, intV 7, .cell Cell.empty, .slice (Slice.ofCell Cell.empty), .tuple #[], .cont (.quit 0)]

private def genBtosFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    (mkCase "fuzz/underflow" #[], rng1)
  else if shape = 1 then
    (mkCase "fuzz/type-null" #[.null], rng1)
  else if shape = 2 then
    (mkCase "fuzz/type-int" #[intV 9], rng1)
  else if shape = 3 then
    (mkCase "fuzz/type-cell" #[.cell Cell.empty], rng1)
  else if shape = 4 then
    (mkCase "fuzz/type-slice" #[.slice (Slice.ofCell Cell.empty)], rng1)
  else if shape = 5 then
    (mkCase "fuzz/ok/empty-builder" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    let (b, rng2) := genBuilderMixed rng1
    (mkCase "fuzz/ok/random-builder" #[.builder b], rng2)
  else if shape = 7 then
    let (b, rng2) := genBuilderMixed rng1
    let (noise, rng3) := pickFromPool fuzzNoisePool rng2
    (mkCase "fuzz/ok/deep-noise" #[noise, .builder b], rng3)
  else if shape = 8 then
    let (b, rng2) := genBuilderMixed rng1
    let stack : Array Value := #[.null, intV (-3), .tuple #[], .builder b]
    (mkCase "fuzz/ok/deep-fixed" stack, rng2)
  else
    let (b, rng2) := genBuilderMixed rng1
    (mkCase "fuzz/ok/deep-with-slice" #[.slice (Slice.ofCell Cell.empty), .builder b], rng2)

def suite : InstrSuite where
  id := btosId
  unit := #[]
  oracle := #[
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-int" #[intV 7],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "type/top-slice" #[.slice (Slice.ofCell Cell.empty)],
    mkCase "ok/direct/empty-builder" #[.builder Builder.empty],
    mkCase "ok/program/bits13-zeros" #[]
      #[.newc, .pushInt (.num 13), .stZeroes, btosInstr],
    mkCase "ok/program/refs2-only" #[.cell refLeafA, .cell refLeafB]
      #[.newc, .stref, .stref, btosInstr],
    mkCase "ok/program/bits7-plus-ref1" #[.cell refLeafA]
      #[.newc, .pushInt (.num 7), .stZeroes, .stref, btosInstr],
    mkCase "gas/exact-cost-succeeds" #[.builder Builder.empty]
      #[.pushInt (.num btosSetGasExact), .tonEnvOp .setGasLimit, btosInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty]
      #[.pushInt (.num btosSetGasExactMinusOne), .tonEnvOp .setGasLimit, btosInstr]
  ]
  fuzz := #[
    { seed := 2026021101
      count := 500
      gen := genBtosFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BTOS
