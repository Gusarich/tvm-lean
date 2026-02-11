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
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.BTOS
